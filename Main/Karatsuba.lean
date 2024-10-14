import Mathlib.Data.Nat.Log

def M (m n : ℕ) : ℕ := Id.run do
  let l : ℕ := max (Nat.log 10 m) (Nat.log 10 n)
  if l < 4 then
    m * n
  else
    let h := l / 2
    let a := m / (10^l)
    let b := m - a * 10^h
    let c := n / (10^h)
    let d := n - c * 10^h
    let w := M a c
    let x := M b d
    let y := M (a+b) (c+d)
    let z := 10^(2*h) * w + 10^h * (y - w - x) + x
    z
  termination_by (n, m)
  decreasing_by
    simp_wf
    sorry
    sorry
    sorry
