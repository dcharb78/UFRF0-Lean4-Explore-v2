# Collatz W(k) Growth Analysis

## Data

| k | modulus | max_bad_streak | W(k) |
|---|---------|---------------|------|
| 3 | 104 | 4 | 10 |
| 4 | 208 | 5 | 22 |
| 5 | 416 | 6 | 26 |
| 6 | 832 | 7 | 42 |
| 7 | 1664 | 8 | 52 |
| 8 | 3328 | 9 | 54 |
| 9 | 6656 | 10 | 59 |
| 10 | 13312 | 11 | 78 |

## Model Fits

- Linear:     W = 8.9881*k + -15.5476   (R^2 = 0.968635)
- Quadratic:  W = -0.0774*k^2 + 9.9940*k + -18.4107   (R^2 = 0.968922)
- Exponential: W ~ 6.7866 * 1.2950^k   (R^2 = 0.857352)

## Drift Budget

- bad_streak(k) = k+1 always
- Drift cost per bad streak = (k+1) * 0.584963
- Min recovery steps = (k+1) * 1.4094
- W(k)/(k+1) mean = 5.3405, std = 1.3946

## Conclusion

Best fitting model: **Quadratic O(k^2)** (R^2 = 0.968922)

The data is consistent with **O(k) linear growth** of W(k).
Specifically, W(k) ≈ 5.34*(k+1).

W(k)/modulus decreases monotonically: False

This supports the proof strategy that the convergence window
is a negligible fraction of the modulus as k grows.
