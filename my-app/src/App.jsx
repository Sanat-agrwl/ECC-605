import { useState, useMemo, useCallback } from "react";

// ─── Finite Field Arithmetic over F_p ───
function mod(a, p) { return ((a % p) + p) % p; }
function modPow(base, exp, p) {
  let result = 1; base = mod(base, p);
  while (exp > 0) {
    if (exp & 1) result = mod(result * base, p);
    exp >>= 1; base = mod(base * base, p);
  }
  return result;
}
function modInv(a, p) { return modPow(a, p - 2, p); }

// ─── Polynomial evaluation ───
function polyEval(coeffs, x, p) {
  let result = 0, xPow = 1;
  for (const c of coeffs) {
    result = mod(result + mod(c * xPow, p), p);
    xPow = mod(xPow * x, p);
  }
  return result;
}

// ─── Lagrange interpolation at x=0 ───
function lagrangeAt0(points, p) {
  let result = 0;
  for (let j = 0; j < points.length; j++) {
    let num = 1, den = 1;
    for (let m = 0; m < points.length; m++) {
      if (m === j) continue;
      num = mod(num * mod(-points[m][0], p), p);
      den = mod(den * mod(points[j][0] - points[m][0], p), p);
    }
    const lambda = mod(num * modInv(den, p), p);
    result = mod(result + mod(points[j][1] * lambda, p), p);
  }
  return result;
}

// ─── Berlekamp-Welch style error correction ───
function tryRecoverWithErrors(shares, t, p) {
  const n = shares.length;
  const votes = {};

  // For manageable sizes, enumerate ALL C(n,t) subsets (up to ~5000)
  function comb(n, k) {
    if (k > n || k < 0) return 0;
    if (k === 0 || k === n) return 1;
    let r = 1;
    for (let i = 0; i < k; i++) r = r * (n - i) / (i + 1);
    return Math.round(r);
  }

  const totalSubsets = comb(n, t);

  if (totalSubsets <= 5000) {
    // Enumerate all subsets
    function enumerate(start, chosen) {
      if (chosen.length === t) {
        const pts = chosen.map(i => shares[i]);
        const s = lagrangeAt0(pts, p);
        votes[s] = (votes[s] || 0) + 1;
        return;
      }
      const remaining = t - chosen.length;
      for (let i = start; i <= n - remaining; i++) {
        chosen.push(i);
        enumerate(i + 1, chosen);
        chosen.pop();
      }
    }
    enumerate(0, []);
  } else {
    // Random sampling with xorshift128 for quality randomness
    let x = 123456789, y = 362436069, z = 521288629, w = 88675123;
    function xorshift() {
      const t = x ^ (x << 11);
      x = y; y = z; z = w;
      w = (w ^ (w >>> 19)) ^ (t ^ (t >>> 8));
      return (w >>> 0);
    }
    const NUM_TRIALS = 1000;
    for (let trial = 0; trial < NUM_TRIALS; trial++) {
      const indices = Array.from({ length: n }, (_, i) => i);
      for (let i = n - 1; i > 0; i--) {
        const j = xorshift() % (i + 1);
        [indices[i], indices[j]] = [indices[j], indices[i]];
      }
      const subset = indices.slice(0, t);
      const pts = subset.map(i => shares[i]);
      const s = lagrangeAt0(pts, p);
      votes[s] = (votes[s] || 0) + 1;
    }
  }

  let bestSecret = -1, bestCount = 0, totalVotes = 0;
  for (const [s, count] of Object.entries(votes)) {
    totalVotes += count;
    if (count > bestCount) { bestCount = count; bestSecret = parseInt(s); }
  }
  return { secret: bestSecret, confidence: bestCount / totalVotes };
}

const PRIMES = [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47];

// ─── Tab Button ───
function TabBtn({ active, onClick, children }) {
  return (
    <button onClick={onClick} style={{
      padding: "10px 20px", border: "none", cursor: "pointer",
      fontFamily: "'JetBrains Mono', monospace", fontSize: "13px", fontWeight: 600,
      color: active ? "#fff" : "#8892b0",
      background: active ? "linear-gradient(135deg, #e94560, #c23152)" : "transparent",
      borderRadius: "8px", transition: "all 0.3s ease",
      letterSpacing: "0.5px"
    }}>{children}</button>
  );
}

// ─── Styled components ───
function Card({ children, style }) {
  return <div style={{
    background: "rgba(17, 25, 40, 0.75)", borderRadius: "12px",
    border: "1px solid rgba(233, 69, 96, 0.15)", padding: "20px",
    backdropFilter: "blur(10px)", ...style
  }}>{children}</div>;
}

function Label({ children }) {
  return <span style={{ color: "#8892b0", fontSize: "12px", fontWeight: 600,
    textTransform: "uppercase", letterSpacing: "1.5px", fontFamily: "'JetBrains Mono', monospace"
  }}>{children}</span>;
}

function Slider({ label, value, onChange, min, max, displayVal }) {
  return (
    <div style={{ marginBottom: "14px" }}>
      <div style={{ display: "flex", justifyContent: "space-between", marginBottom: "6px" }}>
        <Label>{label}</Label>
        <span style={{ color: "#e94560", fontFamily: "'JetBrains Mono', monospace", fontSize: "14px", fontWeight: 700 }}>
          {displayVal ?? value}
        </span>
      </div>
      <input type="range" min={min} max={max} value={value} onChange={e => onChange(+e.target.value)}
        style={{ width: "100%", accentColor: "#e94560" }} />
    </div>
  );
}

// ════════════════════════════════════
// TAB 1: Secret Sharing Simulator
// ════════════════════════════════════
function SecretSharingTab() {
  const [secret, setSecret] = useState(4);
  const [threshold, setThreshold] = useState(3);
  const [numShares, setNumShares] = useState(7);
  const [corruptCount, setCorruptCount] = useState(0);
  const [seed, setSeed] = useState(42);

  const p = useMemo(() => PRIMES.find(pr => pr > numShares && pr > secret) || 47, [numShares, secret]);

  const { coeffs, shares, corrupted, recovered, trueSecret } = useMemo(() => {
    // Seeded PRNG
    let s = seed;
    const rand = () => { s = (s * 1103515245 + 12345) & 0x7fffffff; return s; };

    const coeffs = [mod(secret, p)];
    for (let i = 1; i < threshold; i++) coeffs.push(mod(rand(), p));

    const shares = [];
    for (let i = 1; i <= numShares; i++) shares.push([i, polyEval(coeffs, i, p)]);

    const corrupted = shares.map(([x, y]) => [x, y]);
    const corruptedIdx = new Set();
    let attempts = 0;
    while (corruptedIdx.size < Math.min(corruptCount, numShares) && attempts < 100) {
      corruptedIdx.add(rand() % numShares);
      attempts++;
    }
    for (const idx of corruptedIdx) {
      corrupted[idx] = [corrupted[idx][0], mod(corrupted[idx][1] + 1 + (rand() % (p - 1)), p)];
    }

    let recovered;
    if (corruptCount === 0) {
      recovered = { secret: lagrangeAt0(corrupted.slice(0, threshold), p), confidence: 1 };
    } else {
      recovered = tryRecoverWithErrors(corrupted, threshold, p);
    }

    return { coeffs, shares, corrupted, recovered, trueSecret: mod(secret, p) };
  }, [secret, threshold, numShares, corruptCount, seed, p]);

  const maxCorrupt = Math.floor((numShares - threshold) / 2);

  // Generate polynomial curve points for visualization
  const curvePoints = useMemo(() => {
    const pts = [];
    for (let x = 0; x <= numShares + 1; x += 0.1) {
      pts.push({ x, y: polyEval(coeffs, x, p) });
    }
    return pts;
  }, [coeffs, numShares, p]);

  return (
    <div style={{ display: "grid", gridTemplateColumns: "280px 1fr", gap: "20px" }}>
      <Card>
        <h3 style={{ color: "#e94560", margin: "0 0 16px", fontSize: "15px", fontFamily: "'JetBrains Mono', monospace" }}>
          Parameters
        </h3>
        <Slider label="Secret s" value={secret} onChange={setSecret} min={0} max={p - 1} />
        <Slider label="Threshold t" value={threshold}
          onChange={setThreshold}
          min={2} max={Math.min(numShares, 8)} />
        <Slider label="Shares n" value={numShares}
          onChange={setNumShares}
          min={threshold + 1} max={12} />
        <Slider label="Corrupted" value={corruptCount} onChange={setCorruptCount}
          min={0} max={numShares} />
        <div style={{ marginTop: "8px", padding: "10px", background: "rgba(233,69,96,0.08)", borderRadius: "8px", fontSize: "12px", color: "#8892b0", fontFamily: "'JetBrains Mono', monospace" }}>
          <div>Field: 𝔽<sub>{p}</sub></div>
          <div>RS distance: d = {numShares - threshold + 1}</div>
          <div>Max correctable: ⌊(d-1)/2⌋ = {maxCorrupt}</div>
          {corruptCount > maxCorrupt && (
            <div style={{ color: "#ff5050", marginTop: "6px", fontWeight: 700 }}>
              ⚠ Exceeds error-correction capacity!
              {corruptCount > numShares - threshold && " Not enough clean shares for interpolation."}
            </div>
          )}
        </div>
        <button onClick={() => setSeed(s => s + 1)} style={{
          marginTop: "12px", width: "100%", padding: "10px", border: "1px solid rgba(233,69,96,0.3)",
          borderRadius: "8px", background: "transparent", color: "#e94560", cursor: "pointer",
          fontFamily: "'JetBrains Mono', monospace", fontSize: "12px", fontWeight: 600
        }}>↻ Randomize Coefficients</button>
      </Card>

      <div style={{ display: "flex", flexDirection: "column", gap: "16px" }}>
        <Card>
          <h3 style={{ color: "#ccd6f6", margin: "0 0 4px", fontSize: "14px", fontFamily: "'JetBrains Mono', monospace" }}>
            f(x) = {coeffs.map((c, i) => `${c}${i === 0 ? '' : `x${i > 1 ? `^${i}` : ''}`}`).join(' + ')} mod {p}
          </h3>
          <div style={{ fontSize: "11px", color: "#8892b0", marginBottom: "12px", fontFamily: "'JetBrains Mono', monospace" }}>
            f(0) = {trueSecret} = secret ✓
          </div>
          {/* Share visualization */}
          <div style={{ display: "flex", gap: "8px", flexWrap: "wrap" }}>
            {corrupted.map(([x, y], i) => {
              const isCorrupted = y !== shares[i][1];
              return (
                <div key={i} style={{
                  padding: "8px 12px", borderRadius: "8px", fontSize: "13px",
                  fontFamily: "'JetBrains Mono', monospace", fontWeight: 600,
                  background: isCorrupted ? "rgba(255, 80, 80, 0.15)" : "rgba(100, 255, 218, 0.08)",
                  border: `1px solid ${isCorrupted ? "rgba(255, 80, 80, 0.4)" : "rgba(100, 255, 218, 0.2)"}`,
                  color: isCorrupted ? "#ff5050" : "#64ffda"
                }}>
                  s<sub>{x}</sub> = {y} {isCorrupted ? "✗" : "✓"}
                </div>
              );
            })}
          </div>
        </Card>

        <Card style={{ flex: 1 }}>
          <h3 style={{ color: "#ccd6f6", margin: "0 0 12px", fontSize: "14px", fontFamily: "'JetBrains Mono', monospace" }}>
            Reconstruction Result
          </h3>
          <div style={{ display: "flex", gap: "24px", alignItems: "center" }}>
            <div style={{
              width: "100px", height: "100px", borderRadius: "50%",
              display: "flex", flexDirection: "column", alignItems: "center", justifyContent: "center",
              background: recovered.secret === trueSecret
                ? "linear-gradient(135deg, rgba(100,255,218,0.15), rgba(100,255,218,0.05))"
                : "linear-gradient(135deg, rgba(255,80,80,0.15), rgba(255,80,80,0.05))",
              border: `2px solid ${recovered.secret === trueSecret ? "#64ffda" : "#ff5050"}`
            }}>
              <div style={{ fontSize: "28px", fontWeight: 800, color: recovered.secret === trueSecret ? "#64ffda" : "#ff5050",
                fontFamily: "'JetBrains Mono', monospace" }}>{recovered.secret}</div>
              <div style={{ fontSize: "10px", color: "#8892b0", fontFamily: "'JetBrains Mono', monospace" }}>
                {recovered.secret === trueSecret ? "CORRECT" : "FAILED"}
              </div>
            </div>
            <div style={{ fontSize: "13px", color: "#8892b0", lineHeight: 1.8, fontFamily: "'JetBrains Mono', monospace" }}>
              <div>True secret: <span style={{ color: "#64ffda" }}>{trueSecret}</span></div>
              <div>Recovered: <span style={{ color: recovered.secret === trueSecret ? "#64ffda" : "#ff5050" }}>{recovered.secret}</span></div>
              <div>Confidence: <span style={{ color: "#e94560" }}>{(recovered.confidence * 100).toFixed(1)}%</span></div>
              <div>Corruptions: {corruptCount} / max correctable: {maxCorrupt}</div>
            </div>
          </div>
        </Card>
      </div>
    </div>
  );
}

// ════════════════════════════════════
// TAB 2: PIR Protocol Demo
// ════════════════════════════════════
function PIRTab() {
  const [dbSize, setDbSize] = useState(8);
  const [targetIdx, setTargetIdx] = useState(3);
  const [step, setStep] = useState(0);
  const [seed, setSeed] = useState(1);

  const { db, S, S2, a1, a2, result } = useMemo(() => {
    // xorshift128 for quality randomness
    let x = 123456789 + seed * 17, y = 362436069 + seed * 31, z = 521288629, w = 88675123 + seed * 53;
    function xor128() {
      const t = x ^ (x << 11);
      x = y; y = z; z = w;
      w = (w ^ (w >>> 19)) ^ (t ^ (t >>> 8));
      return (w >>> 0);
    }

    const db = Array.from({ length: dbSize }, () => xor128() % 2);
    const S = Array.from({ length: dbSize }, () => xor128() % 2);
    const idx = Math.min(targetIdx, dbSize - 1);
    const S2 = S.map((b, i) => i === idx ? b ^ 1 : b);

    const a1 = S.reduce((acc, b, i) => acc ^ (b & db[i]), 0);
    const a2 = S2.reduce((acc, b, i) => acc ^ (b & db[i]), 0);

    return { db, S, S2, a1, a2, result: a1 ^ a2 };
  }, [dbSize, targetIdx, seed]);

  const idx = Math.min(targetIdx, dbSize - 1);

  return (
    <div style={{ display: "grid", gridTemplateColumns: "250px 1fr", gap: "20px" }}>
      <Card>
        <h3 style={{ color: "#e94560", margin: "0 0 16px", fontSize: "15px", fontFamily: "'JetBrains Mono', monospace" }}>
          Setup
        </h3>
        <Slider label="DB size N" value={dbSize} onChange={v => { setDbSize(v); if (targetIdx >= v) setTargetIdx(v - 1); }} min={4} max={16} />
        <Slider label="Target index i" value={targetIdx} onChange={setTargetIdx} min={0} max={dbSize - 1} />

        <div style={{ marginTop: "12px" }}>
          <Label>Database x</Label>
          <div style={{ display: "flex", gap: "4px", marginTop: "6px", flexWrap: "wrap" }}>
            {db.map((b, i) => (
              <div key={i} style={{
                width: "28px", height: "28px", borderRadius: "6px", display: "flex",
                alignItems: "center", justifyContent: "center", fontSize: "13px",
                fontFamily: "'JetBrains Mono', monospace", fontWeight: 700,
                background: i === idx ? "rgba(233, 69, 96, 0.2)" : "rgba(100, 255, 218, 0.06)",
                border: `1px solid ${i === idx ? "#e94560" : "rgba(100, 255, 218, 0.15)"}`,
                color: i === idx ? "#e94560" : "#64ffda"
              }}>{b}</div>
            ))}
          </div>
          <div style={{ fontSize: "11px", color: "#8892b0", marginTop: "6px", fontFamily: "'JetBrains Mono', monospace" }}>
            x[{idx}] = {db[idx]} ← target
          </div>
        </div>

        <button onClick={() => { setSeed(s => s + 1); setStep(0); }} style={{
          marginTop: "12px", width: "100%", padding: "8px", border: "1px solid rgba(233,69,96,0.3)",
          borderRadius: "8px", background: "transparent", color: "#e94560", cursor: "pointer",
          fontFamily: "'JetBrains Mono', monospace", fontSize: "12px", fontWeight: 600
        }}>↻ Randomize DB &amp; Query</button>

        <div style={{ display: "flex", gap: "8px", marginTop: "10px" }}>
          <button onClick={() => setStep(Math.max(0, step - 1))} style={{
            flex: 1, padding: "8px", border: "1px solid rgba(233,69,96,0.3)", borderRadius: "6px",
            background: "transparent", color: "#e94560", cursor: "pointer",
            fontFamily: "'JetBrains Mono', monospace", fontSize: "12px"
          }}>← Prev</button>
          <button onClick={() => setStep(Math.min(4, step + 1))} style={{
            flex: 1, padding: "8px", border: "none", borderRadius: "6px",
            background: "linear-gradient(135deg, #e94560, #c23152)", color: "#fff", cursor: "pointer",
            fontFamily: "'JetBrains Mono', monospace", fontSize: "12px", fontWeight: 600
          }}>Next →</button>
        </div>
      </Card>

      <div style={{ display: "flex", flexDirection: "column", gap: "12px" }}>
        {[
          { title: "Step 1: User picks random S", content: (
            <div>
              <div style={{ color: "#8892b0", fontSize: "13px", marginBottom: "8px" }}>User generates a uniformly random subset S ⊆ [N]:</div>
              <div style={{ display: "flex", gap: "4px", flexWrap: "wrap" }}>
                {S.map((b, i) => (
                  <span key={i} style={{
                    padding: "4px 8px", borderRadius: "4px", fontSize: "12px",
                    fontFamily: "'JetBrains Mono', monospace", background: b ? "rgba(100,255,218,0.12)" : "transparent",
                    color: b ? "#64ffda" : "#4a5568", border: `1px solid ${b ? "rgba(100,255,218,0.2)" : "rgba(255,255,255,0.05)"}`
                  }}>{i}</span>
                ))}
              </div>
              <div style={{ color: "#64ffda", fontSize: "12px", marginTop: "6px", fontFamily: "'JetBrains Mono', monospace" }}>
                S = {"{"}{S.map((b, i) => b ? i : null).filter(x => x !== null).join(", ")}{"}"}
              </div>
            </div>
          )},
          { title: "Step 2: Construct queries", content: (
            <div style={{ display: "grid", gridTemplateColumns: "1fr 1fr", gap: "12px" }}>
              <div>
                <Label>Query to Server 1: S</Label>
                <div style={{ display: "flex", gap: "3px", marginTop: "6px", flexWrap: "wrap" }}>
                  {S.map((b, i) => (
                    <span key={i} style={{
                      padding: "3px 6px", borderRadius: "3px", fontSize: "11px",
                      fontFamily: "'JetBrains Mono', monospace",
                      background: b ? "rgba(100,255,218,0.12)" : "transparent",
                      color: b ? "#64ffda" : "#4a5568"
                    }}>{b}</span>
                  ))}
                </div>
              </div>
              <div>
                <Label>Query to Server 2: S⊕{"{"}i{"}"}</Label>
                <div style={{ display: "flex", gap: "3px", marginTop: "6px", flexWrap: "wrap" }}>
                  {S2.map((b, i) => (
                    <span key={i} style={{
                      padding: "3px 6px", borderRadius: "3px", fontSize: "11px",
                      fontFamily: "'JetBrains Mono', monospace",
                      background: b ? "rgba(233,69,96,0.15)" : "transparent",
                      color: b ? "#e94560" : "#4a5568",
                      border: i === idx ? "1px solid #e94560" : "none"
                    }}>{b}</span>
                  ))}
                </div>
                <div style={{ fontSize: "11px", color: "#8892b0", marginTop: "4px", fontFamily: "'JetBrains Mono', monospace" }}>
                  Bit {idx} is toggled: {S[idx]} → {S2[idx]}
                </div>
              </div>
            </div>
          )},
          { title: "Step 3: Servers compute answers", content: (
            <div style={{ display: "grid", gridTemplateColumns: "1fr 1fr", gap: "12px" }}>
              <div style={{ padding: "12px", background: "rgba(100,255,218,0.04)", borderRadius: "8px" }}>
                <Label>Server 1</Label>
                <div style={{ color: "#64ffda", fontSize: "13px", marginTop: "6px", fontFamily: "'JetBrains Mono', monospace" }}>
                  a₁ = ⊕ x[S] = {S.map((b, i) => b ? `x[${i}]` : null).filter(Boolean).join(" ⊕ ")}
                </div>
                <div style={{ color: "#64ffda", fontSize: "18px", fontWeight: 800, marginTop: "4px", fontFamily: "'JetBrains Mono', monospace" }}>= {a1}</div>
              </div>
              <div style={{ padding: "12px", background: "rgba(233,69,96,0.04)", borderRadius: "8px" }}>
                <Label>Server 2</Label>
                <div style={{ color: "#e94560", fontSize: "13px", marginTop: "6px", fontFamily: "'JetBrains Mono', monospace" }}>
                  a₂ = ⊕ x[S⊕i] = {S2.map((b, i) => b ? `x[${i}]` : null).filter(Boolean).join(" ⊕ ")}
                </div>
                <div style={{ color: "#e94560", fontSize: "18px", fontWeight: 800, marginTop: "4px", fontFamily: "'JetBrains Mono', monospace" }}>= {a2}</div>
              </div>
            </div>
          )},
          { title: "Step 4: User recovers x[i]", content: (
            <div style={{ textAlign: "center", padding: "16px" }}>
              <div style={{ fontSize: "20px", fontFamily: "'JetBrains Mono', monospace", color: "#ccd6f6" }}>
                a₁ ⊕ a₂ = {a1} ⊕ {a2} = <span style={{ color: "#64ffda", fontSize: "28px", fontWeight: 800 }}>{result}</span>
              </div>
              <div style={{ fontSize: "13px", color: "#8892b0", marginTop: "8px", fontFamily: "'JetBrains Mono', monospace" }}>
                x[{idx}] = {db[idx]} {result === db[idx] ? "✓ Correct!" : "✗ Error"}
              </div>
            </div>
          )},
          { title: "Privacy check", content: (
            <div>
              <div style={{ color: "#8892b0", fontSize: "13px", marginBottom: "8px", lineHeight: 1.6 }}>
                Each server sees a <span style={{ color: "#64ffda" }}>uniformly random</span> subset.
                Since S is random, S⊕{"{"}i{"}"} is also random. Neither server can determine i.
              </div>
              <div style={{ display: "grid", gridTemplateColumns: "1fr 1fr", gap: "12px" }}>
                <div style={{ padding: "10px", background: "rgba(100,255,218,0.04)", borderRadius: "8px", textAlign: "center" }}>
                  <div style={{ fontSize: "11px", color: "#8892b0", fontFamily: "'JetBrains Mono', monospace" }}>Server 1 sees</div>
                  <div style={{ fontSize: "14px", color: "#64ffda", fontFamily: "'JetBrains Mono', monospace" }}>Random query → No info about i</div>
                </div>
                <div style={{ padding: "10px", background: "rgba(233,69,96,0.04)", borderRadius: "8px", textAlign: "center" }}>
                  <div style={{ fontSize: "11px", color: "#8892b0", fontFamily: "'JetBrains Mono', monospace" }}>Server 2 sees</div>
                  <div style={{ fontSize: "14px", color: "#e94560", fontFamily: "'JetBrains Mono', monospace" }}>Random query → No info about i</div>
                </div>
              </div>
            </div>
          )}
        ].map((s, i) => (
          <Card key={i} style={{
            opacity: i <= step ? 1 : 0.3, transition: "all 0.3s ease",
            border: i === step ? "1px solid rgba(233, 69, 96, 0.4)" : "1px solid rgba(233, 69, 96, 0.1)"
          }}>
            <h4 style={{ color: "#ccd6f6", margin: "0 0 8px", fontSize: "13px", fontFamily: "'JetBrains Mono', monospace" }}>
              {s.title}
            </h4>
            {i <= step && s.content}
          </Card>
        ))}
      </div>
    </div>
  );
}

// ════════════════════════════════════
// TAB 3: Hadamard LDC Demo
// ════════════════════════════════════
function LDCTab() {
  const [msgBits, setMsgBits] = useState([1, 0, 1, 1]);
  const [noiseRate, setNoiseRate] = useState(0);
  const [trialCount, setTrialCount] = useState(50);

  const N = msgBits.length;
  const M = 1 << N; // 2^N

  const { codeword, noisyCodeword, decodingResults } = useMemo(() => {
    const codeword = [];
    for (let r = 0; r < M; r++) {
      let dot = 0;
      for (let j = 0; j < N; j++) {
        if ((r >> j) & 1) dot ^= msgBits[j];
      }
      codeword.push(dot);
    }

    let seed = 77;
    const rand = () => { seed = (seed * 1103515245 + 12345) & 0x7fffffff; return seed; };

    const noisy = codeword.map(b => (rand() % 100) < noiseRate ? b ^ 1 : b);

    const results = [];
    for (let targetBit = 0; targetBit < N; targetBit++) {
      let correct = 0;
      const ei = 1 << targetBit;
      for (let trial = 0; trial < trialCount; trial++) {
        const r = rand() % M;
        const rPrime = r ^ ei;
        const decoded = noisy[r] ^ noisy[rPrime];
        if (decoded === msgBits[targetBit]) correct++;
      }
      results.push({ bit: targetBit, actual: msgBits[targetBit], successRate: correct / trialCount });
    }

    return { codeword, noisyCodeword: noisy, decodingResults: results };
  }, [msgBits, noiseRate, trialCount]);

  const toggleBit = (i) => {
    const newBits = [...msgBits];
    newBits[i] ^= 1;
    setMsgBits(newBits);
  };

  const errCount = codeword.reduce((acc, b, i) => acc + (b !== noisyCodeword[i] ? 1 : 0), 0);

  return (
    <div style={{ display: "grid", gridTemplateColumns: "260px 1fr", gap: "20px" }}>
      <Card>
        <h3 style={{ color: "#e94560", margin: "0 0 16px", fontSize: "15px", fontFamily: "'JetBrains Mono', monospace" }}>
          Hadamard LDC
        </h3>
        <Label>Message x (click to toggle)</Label>
        <div style={{ display: "flex", gap: "6px", margin: "8px 0 16px" }}>
          {msgBits.map((b, i) => (
            <button key={i} onClick={() => toggleBit(i)} style={{
              width: "40px", height: "40px", borderRadius: "8px", border: "1px solid rgba(100,255,218,0.3)",
              background: b ? "rgba(100,255,218,0.15)" : "transparent",
              color: b ? "#64ffda" : "#4a5568", fontSize: "16px", fontWeight: 700,
              cursor: "pointer", fontFamily: "'JetBrains Mono', monospace"
            }}>{b}</button>
          ))}
        </div>
        <Slider label="Noise %" value={noiseRate} onChange={setNoiseRate} min={0} max={45} displayVal={`${noiseRate}%`} />
        <Slider label="Trials per bit" value={trialCount} onChange={setTrialCount} min={10} max={200} />

        <div style={{ marginTop: "8px", padding: "10px", background: "rgba(233,69,96,0.08)", borderRadius: "8px",
          fontSize: "12px", color: "#8892b0", fontFamily: "'JetBrains Mono', monospace", lineHeight: 1.6 }}>
          <div>N = {N} message bits</div>
          <div>M = 2<sup>N</sup> = {M} codeword bits</div>
          <div>Queries per decode: 2</div>
          <div>Errors introduced: {errCount}/{M}</div>
        </div>
      </Card>

      <div style={{ display: "flex", flexDirection: "column", gap: "16px" }}>
        <Card>
          <h4 style={{ color: "#ccd6f6", margin: "0 0 10px", fontSize: "13px", fontFamily: "'JetBrains Mono', monospace" }}>
            Codeword c(x) = {"{"} ⟨x, r⟩ : r ∈ {"{"}0,1{"}"}<sup>{N}</sup> {"}"}
          </h4>
          <div style={{ display: "flex", gap: "3px", flexWrap: "wrap" }}>
            {codeword.map((b, i) => (
              <span key={i} style={{
                width: "22px", height: "22px", borderRadius: "4px", display: "inline-flex",
                alignItems: "center", justifyContent: "center", fontSize: "10px",
                fontFamily: "'JetBrains Mono', monospace",
                background: noisyCodeword[i] !== b ? "rgba(255,80,80,0.2)" : (b ? "rgba(100,255,218,0.1)" : "rgba(255,255,255,0.03)"),
                color: noisyCodeword[i] !== b ? "#ff5050" : (b ? "#64ffda" : "#4a5568"),
                border: noisyCodeword[i] !== b ? "1px solid rgba(255,80,80,0.3)" : "1px solid transparent"
              }}>{noisyCodeword[i]}</span>
            ))}
          </div>
          {noiseRate > 0 && (
            <div style={{ fontSize: "11px", color: "#ff5050", marginTop: "6px", fontFamily: "'JetBrains Mono', monospace" }}>
              Red = corrupted positions ({errCount} errors)
            </div>
          )}
        </Card>

        <Card style={{ flex: 1 }}>
          <h4 style={{ color: "#ccd6f6", margin: "0 0 12px", fontSize: "13px", fontFamily: "'JetBrains Mono', monospace" }}>
            Local Decoding Results (2 queries per bit, {trialCount} trials each)
          </h4>
          <div style={{ display: "flex", flexDirection: "column", gap: "10px" }}>
            {decodingResults.map(r => (
              <div key={r.bit} style={{ display: "flex", alignItems: "center", gap: "12px" }}>
                <div style={{ width: "60px", fontSize: "13px", color: "#8892b0", fontFamily: "'JetBrains Mono', monospace" }}>
                  x[{r.bit}] = {r.actual}
                </div>
                <div style={{ flex: 1, height: "28px", background: "rgba(255,255,255,0.03)", borderRadius: "6px", overflow: "hidden", position: "relative" }}>
                  <div style={{
                    height: "100%", width: `${r.successRate * 100}%`, borderRadius: "6px",
                    background: r.successRate > 0.8 ? "linear-gradient(90deg, #64ffda, #4ad8b0)" :
                      r.successRate > 0.6 ? "linear-gradient(90deg, #ffd700, #e9a000)" :
                      "linear-gradient(90deg, #ff5050, #e94560)",
                    transition: "width 0.5s ease"
                  }} />
                  <span style={{
                    position: "absolute", right: "8px", top: "50%", transform: "translateY(-50%)",
                    fontSize: "11px", fontWeight: 700, color: "#fff",
                    fontFamily: "'JetBrains Mono', monospace"
                  }}>{(r.successRate * 100).toFixed(0)}%</span>
                </div>
              </div>
            ))}
          </div>
          <div style={{ marginTop: "12px", fontSize: "12px", color: "#8892b0", fontFamily: "'JetBrains Mono', monospace", lineHeight: 1.6 }}>
            Decoding: pick random r, query c[r] and c[r ⊕ eᵢ], output their XOR.
            {noiseRate > 0 && ` With ${noiseRate}% noise, success ≈ ${(100 - 2 * noiseRate).toFixed(0)}% (each query hits an error independently with prob ${noiseRate}%).`}
          </div>
        </Card>
      </div>
    </div>
  );
}

// ════════════════════════════════════
// MAIN APP
// ════════════════════════════════════
export default function App() {
  const [tab, setTab] = useState(0);

  return (
    <div style={{
      minHeight: "100vh", background: "#0a192f", color: "#ccd6f6",
      fontFamily: "'Inter', sans-serif", padding: "24px"
    }}>
      <link href="https://fonts.googleapis.com/css2?family=JetBrains+Mono:wght@400;600;700;800&family=Inter:wght@400;500;600&display=swap" rel="stylesheet" />

      <div style={{ maxWidth: "960px", margin: "0 auto" }}>
        {/* Header */}
        <div style={{ marginBottom: "24px" }}>
          <h1 style={{
            fontSize: "22px", fontWeight: 800, margin: 0,
            fontFamily: "'JetBrains Mono', monospace",
            background: "linear-gradient(135deg, #e94560, #64ffda)",
            WebkitBackgroundClip: "text", WebkitTextFillColor: "transparent"
          }}>
            Secret Sharing · PIR · Locally Decodable Codes
          </h1>
          <p style={{ color: "#8892b0", fontSize: "13px", margin: "6px 0 0",
            fontFamily: "'JetBrains Mono', monospace" }}>
            EE 605 — Interactive Demo
          </p>
        </div>

        {/* Tabs */}
        <div style={{ display: "flex", gap: "8px", marginBottom: "20px",
          background: "rgba(17, 25, 40, 0.6)", padding: "6px", borderRadius: "12px",
          border: "1px solid rgba(233, 69, 96, 0.1)" }}>
          <TabBtn active={tab === 0} onClick={() => setTab(0)}>Shamir's SSS</TabBtn>
          <TabBtn active={tab === 1} onClick={() => setTab(1)}>2-Server PIR</TabBtn>
          <TabBtn active={tab === 2} onClick={() => setTab(2)}>Hadamard LDC</TabBtn>
        </div>

        {/* Content */}
        {tab === 0 && <SecretSharingTab />}
        {tab === 1 && <PIRTab />}
        {tab === 2 && <LDCTab />}
      </div>
    </div>
  );
}