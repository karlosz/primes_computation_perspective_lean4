# Benchmarks of the verified algorithms

## gcd and inverses

### euclid (Alg 2.1.2)
bits of the inputs; bound k(3k+2); expected growth size^2.00
      size     time/run  local exp.
       256      15.2 µs            
       512      34.7 µs        1.19
      1024      78.7 µs        1.18
      2048     163.2 µs        1.05
      4096     393.3 µs        1.27
      8192     946.5 µs        1.27
     16384       2.5 ms        1.38
     32768       7.7 ms        1.64
fitted exponent 1.42 (expected 2.00) ▼

### extEuclid (Alg 2.1.4)
bits of the inputs; bound O(k²); expected growth size^2.00
      size     time/run  local exp.
       256     128.7 µs            
       512     268.4 µs        1.06
      1024     590.2 µs        1.14
      2048       1.1 ms        0.95
      4096       2.6 ms        1.18
      8192       5.8 ms        1.16
     16384      13.8 ms        1.26
     32768      38.3 ms        1.47
fitted exponent 1.29 (expected 2.00) ▼

### modInv (§2.1.1)
bits of the modulus; bound O(k²); expected growth size^2.00
      size     time/run  local exp.
       256     111.8 µs            
       512     280.3 µs        1.33
      1024     540.2 µs        0.95
      2048       1.2 ms        1.14
      4096       2.6 ms        1.10
      8192       5.8 ms        1.18
     16384      13.7 ms        1.24
     32768      38.6 ms        1.49
fitted exponent 1.30 (expected 2.00) ▼

## modular powers

### powMod (Alg 2.1.5)
bits of base, exponent and modulus; bound 2k mulMod(k) = O(k³); expected growth size^3.00
      size     time/run  local exp.
        64      28.0 µs            
       128      69.0 µs        1.30
       256     182.9 µs        1.41
       512     445.1 µs        1.28
      1024       1.4 ms        1.62
      2048       5.7 ms        2.04
      4096      28.0 ms        2.31
fitted exponent 2.00 (expected 3.00) ▼

### pow (in ZMod m) (Alg 2.1.5)
bits of base, exponent and modulus; bound O(k³); expected growth size^3.00
      size     time/run  local exp.
        64      37.6 µs            
       128      88.4 µs        1.23
       256     220.7 µs        1.32
       512     521.0 µs        1.24
      1024       1.5 ms        1.57
      2048       6.0 ms        1.96
      4096      28.9 ms        2.26
fitted exponent 1.93 (expected 3.00) ▼

## Chinese remainders

### garner (Alg 2.1.7)
number of 62-bit moduli; bound O(r²) word operations; expected growth size^2.00
      size     time/run  local exp.
         8     120.8 µs            
        16     261.3 µs        1.11
        32     565.3 µs        1.11
        64       1.2 ms        1.05
       128       2.7 ms        1.18
       256       6.4 ms        1.26
       512      16.9 ms        1.41
      1024      50.5 ms        1.58
fitted exponent 1.42 (expected 2.00) ▼

### crt (Thm 2.1.6)
number of 62-bit moduli; bound O(r²) word operations; expected growth size^2.00
      size     time/run  local exp.
         8     137.8 µs            
        16     269.5 µs        0.97
        32     533.5 µs        0.99
        64       1.2 ms        1.17
       128       3.1 ms        1.38
       256       8.1 ms        1.37
       512      26.3 ms        1.71
fitted exponent 1.47 (expected 2.00) ▼

## quadratic residues and square roots

### jacobi (Alg 2.3.5)
bits of the inputs; bound O(k²); expected growth size^2.00
      size     time/run  local exp.
       256      65.3 µs            
       512     158.1 µs        1.28
      1024     362.9 µs        1.20
      2048     901.0 µs        1.31
      4096       2.3 ms        1.36
      8192       6.7 ms        1.54
     16384      21.3 ms        1.66
     32768      75.4 ms        1.82
fitted exponent 1.67 (expected 2.00) ≈

### sqrtMod (Alg 2.3.8)
bits of the prime p; bound O(k³) (+ O(s² k²) for p - 1 = 2^s t); expected growth size^3.00
      size     time/run  local exp.
        64      34.8 µs            
       128     255.1 µs        2.87
       256     418.1 µs        0.71
       512       1.5 ms        1.88
      1024       1.5 ms       -0.03
      2048       5.9 ms        1.97
fitted exponent 0.97 (expected 3.00) ▼

### cipollaSqrt (Alg 2.3.9)
bits of the prime p; bound O(k³); expected growth size^3.00
      size     time/run  local exp.
        64      51.1 µs            
       128     482.9 µs        3.24
       256       1.2 ms        1.27
       512       2.6 ms        1.19
      1024       3.4 ms        0.35
      2048      10.0 ms        1.56
fitted exponent 0.96 (expected 3.00) ▼

### hensel (Alg 2.3.11)
2^i, the bits of the modulus 7^(2^i) over log₂ 7; bound O(K²) for the last step; expected growth size^2.00
      size     time/run  local exp.
        64      36.7 µs            
       128     127.7 µs        1.80
       256     309.1 µs        1.28
       512     699.2 µs        1.18
      1024       1.5 ms        1.14
      2048       3.2 ms        1.06
      4096       7.0 ms        1.12
      8192      15.8 ms        1.18
fitted exponent 1.12 (expected 2.00) ▼

### cornacchia (Alg 2.3.12)
bits of the prime p ≡ 1 (mod 4); bound O(k³) (the square root); expected growth size^3.00
      size     time/run  local exp.
        64      55.8 µs            
       128     237.1 µs        2.09
       256     400.0 µs        0.75
       512       1.3 ms        1.73
      1024       3.4 ms        1.35
      2048      10.8 ms        1.68
fitted exponent 1.52 (expected 3.00) ▼

## integer square roots

### isqrt (Alg 9.2.11)
bits of N; bound O(log k) divisions, O(k² log k); expected growth size^2.00
      size     time/run  local exp.
       256      23.5 µs            
       512      53.2 µs        1.18
      1024     109.4 µs        1.04
      2048     234.5 µs        1.10
      4096     518.6 µs        1.15
      8192       1.2 ms        1.26
     16384       3.1 ms        1.31
     32768       9.9 ms        1.68
fitted exponent 1.41 (expected 2.00) ▼

## integer multiplication

### Nat.mul (GMP, reference) (§9.5)
bits of the factors; bound (GMP); expected growth size^1.00
      size     time/run  local exp.
      1024       334 ns            
      2048       609 ns        0.87
      4096       1.4 µs        1.17
      8192       4.0 µs        1.54
     16384      11.5 µs        1.53
     32768      27.9 µs        1.28
     65536      80.8 µs        1.54
    131072     218.6 µs        1.43
    262144     440.7 µs        1.01
    524288     995.8 µs        1.18
   1048576       2.1 ms        1.09
fitted exponent 1.23 (expected 1.00) ≈

### karatsuba (Alg 9.5.1)
bits of the factors (2^j); bound O(k^1.585); expected growth size^1.59
      size     time/run  local exp.
        64     112.1 µs            
       128     337.3 µs        1.59
       256       1.0 ms        1.60
       512       3.1 ms        1.58
      1024       9.3 ms        1.60
      2048      27.7 ms        1.58
      4096      82.0 ms        1.57
fitted exponent 1.58 (expected 1.59) ≈

### nussMul (Alg 9.5.25)
bits of the factors; bound 292 k (log₂ k + 3)⁴ (bitModel); expected growth size^1.00
      size     time/run  local exp.
       256       8.1 ms            
       512      17.1 ms        1.08
      1024      35.2 ms        1.04
      2048      76.4 ms        1.12
      4096     154.0 ms        1.01
      8192     315.3 ms        1.03
     16384     647.0 ms        1.04
     32768       2.23 s        1.78
fitted exponent 1.26 (expected 1.00) ≈

## polynomials over finite fields

### Poly.gcd (over F_65537) (Alg 2.2.1)
degree; bound O(d²) field operations; expected growth size^2.00
      size     time/run  local exp.
        32     277.9 µs            
        64       1.0 ms        1.91
       128       4.5 ms        2.10
       256      22.8 ms        2.35
       512     135.9 ms        2.58
      1024     931.9 ms        2.78
fitted exponent 2.68 (expected 2.00) ▲

### isIrreducible (over F_2) (Alg 2.2.9)
degree; bound O(d³) field operations; expected growth size^3.00
      size     time/run  local exp.
        16     480.8 µs            
        32      39.8 µs       -3.59
        64      16.3 ms        8.68
       128       4.3 ms       -1.93
       256     160.2 ms        5.22
fitted exponent 1.65 (expected 3.00) ▼

## polynomial arithmetic over Z_n

### Poly.mul (schoolbook) (§9.6)
number of coefficients (64-bit n); bound d² mulMod; expected growth size^2.00
      size     time/run  local exp.
        32     577.9 µs            
        64       2.4 ms        2.03
       128       9.6 ms        2.02
       256      38.7 ms        2.01
       512     155.6 ms        2.01
      1024     618.0 ms        1.99
fitted exponent 2.00 (expected 2.00) ≈

### mulMod (binary segmentation) (Alg 9.6.1)
number of coefficients (64-bit n); bound one (d log n)-bit product + O(d) small ones; expected growth size^1.00
      size     time/run  local exp.
        32     132.8 µs            
        64     270.9 µs        1.03
       128     532.1 µs        0.97
       256       1.1 ms        1.00
       512       2.2 ms        1.07
      1024       4.5 ms        1.03
      2048       9.4 ms        1.05
      4096      19.0 ms        1.02
      8192      39.7 ms        1.06
fitted exponent 1.04 (expected 1.00) ≈

### invNewton (with mulMod) (Alg 9.6.2)
precision 2^k; bound O(M(2^k)); expected growth size^1.00
      size     time/run  local exp.
        64       1.4 ms            
       128       3.0 ms        1.13
       256       6.4 ms        1.11
       512      14.0 ms        1.13
      1024      31.4 ms        1.17
      2048      69.1 ms        1.14
      4096     148.8 ms        1.11
fitted exponent 1.14 (expected 1.00) ≈

### Poly.modMonic (long division) (§9.6)
degree d of the divisor (dividend 2d); bound O(d²) mulMod; expected growth size^2.00
      size     time/run  local exp.
        32     943.9 µs            
        64       3.7 ms        1.96
       128      14.6 ms        1.99
       256      59.3 ms        2.02
       512     238.4 ms        2.01
      1024     948.1 ms        1.99
fitted exponent 2.00 (expected 2.00) ≈

### fastModMonic (with mulMod) (Alg 9.6.4)
degree d of the divisor (dividend 2d); bound O(M(d)); expected growth size^1.00
      size     time/run  local exp.
        32       1.0 ms            
        64       2.1 ms        1.08
       128       4.5 ms        1.07
       256       9.5 ms        1.09
       512      20.2 ms        1.08
      1024      44.6 ms        1.14
      2048      95.3 ms        1.10
      4096     200.6 ms        1.07
fitted exponent 1.10 (expected 1.00) ≈

## multipoint evaluation

### Horner at each point (§9.6.3)
degree = number of points; bound D² mulMod; expected growth size^2.00
      size     time/run  local exp.
        32     569.3 µs            
        64       2.3 ms        2.02
       128       9.3 ms        2.01
       256      37.4 ms        2.01
       512     148.5 ms        1.99
      1024     590.0 ms        1.99
      2048       2.38 s        2.01
fitted exponent 2.00 (expected 2.00) ≈

### multipointEval (schoolbook products) (Alg 9.6.7)
degree = number of points; bound O(D² log D) mulMod; expected growth size^2.00
      size     time/run  local exp.
        32       1.4 ms            
        64       5.5 ms        1.97
       128      21.8 ms        1.98
       256      84.9 ms        1.96
       512     335.7 ms        1.98
      1024       1.35 s        2.01
fitted exponent 2.00 (expected 2.00) ≈

### multipointEvalFast (Alg 9.6.7)
degree = number of points; bound (log D + 1) nodeBound(D) = Õ(D); expected growth size^1.00
      size     time/run  local exp.
        32       4.5 ms            
        64      12.5 ms        1.45
       128      31.9 ms        1.36
       256      79.0 ms        1.31
       512     190.6 ms        1.27
      1024     452.1 ms        1.25
      2048       1.06 s        1.24
      4096       2.51 s        1.24
fitted exponent 1.24 (expected 1.00) ≈

## sieving

### sievePrimes (§3.2.1)
N; bound O(N log log N) writes; expected growth size^1.00
      size     time/run  local exp.
     16384     259.6 µs            
     32768     474.5 µs        0.87
     65536     882.4 µs        0.89
    131072       1.7 ms        0.98
    262144       3.4 ms        0.99
    524288       7.0 ms        1.03
   1048576      18.7 ms        1.41
   2097152      53.5 ms        1.52
   4194304     119.9 ms        1.17
fitted exponent 1.32 (expected 1.00) ≈

## primality

### isPrimeTD (trial division) (Alg 3.1.1)
bits of the prime; bound √n divisions; expected growth 2^(0.50·bits)
      size     time/run  local exp.
        20       5.0 µs            
        24      17.6 µs        0.45
        28      72.2 µs        0.51
        32     280.5 µs        0.49
        36       1.3 ms        0.57
        40       5.9 ms        0.53
        44      23.2 ms        0.49
fitted exponent 0.53 (expected 0.50) ≈

### millerRabin (4 bases) (Alg 3.5.6)
bits of the prime; bound 4 powMod = O(k³); expected growth size^3.00
      size     time/run  local exp.
        64      91.3 µs            
       128     260.2 µs        1.51
       256     719.3 µs        1.47
       512       1.7 ms        1.25
      1024       4.7 ms        1.46
      2048      17.5 ms        1.88
      4096      80.0 ms        2.20
fitted exponent 1.85 (expected 3.00) ▼

### pocklingtonCheck (Proth primes) (Thm 4.1.3)
bits of n = c·2^m + 1; bound 2 powMod = O(k³); expected growth size^3.00
      size     time/run  local exp.
        64      36.8 µs            
       128      94.0 µs        1.35
       256     241.8 µs        1.36
       512     663.9 µs        1.46
      1024       2.0 ms        1.57
      2048       8.0 ms        2.01
      4096      38.3 ms        2.27
fitted exponent 1.96 (expected 3.00) ▼

### lucasLehmer (Alg 4.2.7)
exponent p of 2^p - 1; bound p squarings mod 2^p - 1 = O(p³); expected growth size^3.00
      size     time/run  local exp.
       128      78.3 µs            
       256     171.8 µs        1.13
       512     362.9 µs        1.08
      1024       1.0 ms        1.50
      2048       4.1 ms        1.99
      4096      19.1 ms        2.24
      8192     105.4 ms        2.46
fitted exponent 2.23 (expected 3.00) ▼

### pepin (Thm 4.1.2)
2^k, the bits of F_k; bound 2^k squarings = O(4^k·2^k); expected growth size^3.00
      size     time/run  local exp.
        64      17.0 µs            
       128      48.2 µs        1.51
       256     127.8 µs        1.41
       512     317.7 µs        1.31
      1024     976.2 µs        1.62
      2048       3.9 ms        2.00
      4096      18.9 ms        2.28
fitted exponent 1.97 (expected 3.00) ▼

## factoring

### trialDivision (Alg 3.1.1)
bits of n = pq (balanced); bound √n divisions; expected growth 2^(0.50·bits)
      size     time/run  local exp.
        20      18.5 µs            
        24      74.7 µs        0.50
        28     285.8 µs        0.48
        32       1.2 ms        0.53
        36       5.0 ms        0.51
        40      22.8 ms        0.54
        44      74.6 ms        0.43
fitted exponent 0.50 (expected 0.50) ≈

### fermat (Alg 5.1.1)
bits of n = pq, q ≈ 2p; bound O(√n) steps; expected growth 2^(0.50·bits)
      size     time/run  local exp.
        20      20.0 µs            
        24      67.4 µs        0.44
        28     281.5 µs        0.52
        32     949.8 µs        0.44
        36       4.4 ms        0.55
        40      15.3 ms        0.45
        44      59.5 ms        0.49
fitted exponent 0.49 (expected 0.50) ≈

### lehman (Alg 5.1.2)
bits of n = pq (balanced); bound (4n^{1/3} + 2) passes, O(n^{1/3} ln³ n); expected growth 2^(0.33·bits)
      size     time/run  local exp.
        20     106.3 µs            
        24     199.5 µs        0.23
        28     360.6 µs        0.21
        32     986.4 µs        0.36
        36       2.9 ms        0.39
        40       9.6 ms        0.43
        44      17.7 ms        0.22
fitted exponent 0.36 (expected 0.33) ≈

### pollardRho (Alg 5.2.1)
bits of n = pq (balanced); bound T passes, T ≈ √p (heuristic); expected growth 2^(0.25·bits)
      size     time/run  local exp.
        40       3.8 ms            
        48      19.9 ms        0.30
        56     112.3 ms        0.31
        64     274.4 ms        0.16
        72       1.70 s        0.33
        80       6.50 s        0.24
           (stopping: slower than 3.00 s per run)
fitted exponent 0.29 (expected 0.25) ≈

### pollardBrent (§5.2.1)
bits of n = pq (balanced); bound 4T steps, T ≈ √p (heuristic); expected growth 2^(0.25·bits)
      size     time/run  local exp.
        40       2.1 ms            
        48      14.6 ms        0.35
        56      68.6 ms        0.28
        64     236.5 ms        0.22
        72       1.76 s        0.36
        80       6.74 s        0.24
           (stopping: slower than 3.00 s per run)
fitted exponent 0.30 (expected 0.25) ≈

### pollardRhoAcc (§5.2.1)
bits of n = pq (balanced); bound T passes, a gcd per 100 (heuristic); expected growth 2^(0.25·bits)
      size     time/run  local exp.
        40       4.8 ms            
        48      23.3 ms        0.28
        56     127.2 ms        0.31
        64     292.9 ms        0.15
        72       1.21 s        0.26
        80       3.81 s        0.21
           (stopping: slower than 3.00 s per run)
fitted exponent 0.23 (expected 0.25) ≈

### pollardStrassen (block by block) (§5.5)
bits of n = pq (balanced); bound B² ≈ √n products; expected growth 2^(0.50·bits)
      size     time/run  local exp.
        20      45.9 µs            
        24     155.6 µs        0.44
        28     506.1 µs        0.43
        32       2.0 ms        0.50
        36       7.9 ms        0.49
        40      31.0 ms        0.49
fitted exponent 0.49 (expected 0.50) ≈

### pollardStrassenFast (§5.5, Thm 5.5.3)
bits of n = pq (balanced); bound 2^35 n^{1/4} (log₂ n + 3)⁷ (nussModel); expected growth 2^(0.25·bits)
      size     time/run  local exp.
        24      27.1 ms            
        28      68.4 ms        0.33
        32     237.7 ms        0.45
        36     620.8 ms        0.35
        40       1.42 s        0.30
        44       3.34 s        0.31
           (stopping: slower than 3.00 s per run)
fitted exponent 0.30 (expected 0.25) ≈

### pollardPMinusOne (Alg 5.4.1)
smoothness bound B (128-bit n, no B-smooth p - 1); bound π(B) log B modular products; expected growth size^1.00
      size     time/run  local exp.
      1024     565.9 µs            
      2048       1.1 ms        0.96
      4096       2.2 ms        1.01
      8192       4.4 ms        0.99
     16384       8.9 ms        1.01
     32768      17.6 ms        0.99
     65536      35.0 ms        0.99
    131072      70.0 ms        1.00
fitted exponent 0.99 (expected 1.00) ≈

### pollardStage2 (§5.4)
second bound B' (B = 1000, 128-bit n); bound O(π(B') log B') products; expected growth size^1.00
      size     time/run  local exp.
      4096       1.2 ms            
      8192       2.1 ms        0.75
     16384       3.7 ms        0.84
     32768       6.8 ms        0.86
     65536      12.7 ms        0.89
    131072      24.0 ms        0.92
    262144      45.8 ms        0.93
fitted exponent 0.92 (expected 1.00) ≈

## discrete logarithms

### bsgs (Alg 5.3.1)
bits of the prime p; bound O(√p) products and table operations; expected growth 2^(0.50·bits)
      size     time/run  local exp.
        34      56.3 ms            
        37     128.1 ms        0.40
        40       1.04 s        1.01
        43       3.80 s        0.62
           (stopping: slower than 3.00 s per run)
fitted exponent 0.82 (expected 0.50) ▲

### rhoLog (§5.2.2)
bits of the prime order N (p = 2N + 1); bound T passes, T ≈ √N (heuristic); expected growth 2^(0.50·bits)
      size     time/run  local exp.
        34     242.5 ms            
        36     749.5 ms        0.81
        38       1.62 s        0.56
        40       4.36 s        0.71
           (stopping: slower than 3.00 s per run)
fitted exponent 0.64 (expected 0.50) ▲

## Summary

| problem | algorithm | bound | expected | fitted | |
|---|---|---|---|---|---|
| gcd and inverses | `euclid` | k(3k+2) | 2.00 | 1.42 | ▼ |
| gcd and inverses | `extEuclid` | O(k²) | 2.00 | 1.29 | ▼ |
| gcd and inverses | `modInv` | O(k²) | 2.00 | 1.30 | ▼ |
| modular powers | `powMod` | 2k mulMod(k) = O(k³) | 3.00 | 2.00 | ▼ |
| modular powers | `pow (in ZMod m)` | O(k³) | 3.00 | 1.93 | ▼ |
| Chinese remainders | `garner` | O(r²) word operations | 2.00 | 1.42 | ▼ |
| Chinese remainders | `crt` | O(r²) word operations | 2.00 | 1.47 | ▼ |
| quadratic residues and square roots | `jacobi` | O(k²) | 2.00 | 1.67 | ≈ |
| quadratic residues and square roots | `sqrtMod` | O(k³) (+ O(s² k²) for p - 1 = 2^s t) | 3.00 | 0.97 | ▼ |
| quadratic residues and square roots | `cipollaSqrt` | O(k³) | 3.00 | 0.96 | ▼ |
| quadratic residues and square roots | `hensel` | O(K²) for the last step | 2.00 | 1.12 | ▼ |
| quadratic residues and square roots | `cornacchia` | O(k³) (the square root) | 3.00 | 1.52 | ▼ |
| integer square roots | `isqrt` | O(log k) divisions, O(k² log k) | 2.00 | 1.41 | ▼ |
| integer multiplication | `Nat.mul (GMP, reference)` | (GMP) | 1.00 | 1.23 | ≈ |
| integer multiplication | `karatsuba` | O(k^1.585) | 1.59 | 1.58 | ≈ |
| integer multiplication | `nussMul` | 292 k (log₂ k + 3)⁴ (bitModel) | 1.00 | 1.26 | ≈ |
| polynomials over finite fields | `Poly.gcd (over F_65537)` | O(d²) field operations | 2.00 | 2.68 | ▲ |
| polynomials over finite fields | `isIrreducible (over F_2)` | O(d³) field operations | 3.00 | 1.65 | ▼ |
| polynomial arithmetic over Z_n | `Poly.mul (schoolbook)` | d² mulMod | 2.00 | 2.00 | ≈ |
| polynomial arithmetic over Z_n | `mulMod (binary segmentation)` | one (d log n)-bit product + O(d) small ones | 1.00 | 1.04 | ≈ |
| polynomial arithmetic over Z_n | `invNewton (with mulMod)` | O(M(2^k)) | 1.00 | 1.14 | ≈ |
| polynomial arithmetic over Z_n | `Poly.modMonic (long division)` | O(d²) mulMod | 2.00 | 2.00 | ≈ |
| polynomial arithmetic over Z_n | `fastModMonic (with mulMod)` | O(M(d)) | 1.00 | 1.10 | ≈ |
| multipoint evaluation | `Horner at each point` | D² mulMod | 2.00 | 2.00 | ≈ |
| multipoint evaluation | `multipointEval (schoolbook products)` | O(D² log D) mulMod | 2.00 | 2.00 | ≈ |
| multipoint evaluation | `multipointEvalFast` | (log D + 1) nodeBound(D) = Õ(D) | 1.00 | 1.24 | ≈ |
| sieving | `sievePrimes` | O(N log log N) writes | 1.00 | 1.32 | ≈ |
| primality | `isPrimeTD (trial division)` | √n divisions | 0.50 | 0.53 | ≈ |
| primality | `millerRabin (4 bases)` | 4 powMod = O(k³) | 3.00 | 1.85 | ▼ |
| primality | `pocklingtonCheck (Proth primes)` | 2 powMod = O(k³) | 3.00 | 1.96 | ▼ |
| primality | `lucasLehmer` | p squarings mod 2^p - 1 = O(p³) | 3.00 | 2.23 | ▼ |
| primality | `pepin` | 2^k squarings = O(4^k·2^k) | 3.00 | 1.97 | ▼ |
| factoring | `trialDivision` | √n divisions | 0.50 | 0.50 | ≈ |
| factoring | `fermat` | O(√n) steps | 0.50 | 0.49 | ≈ |
| factoring | `lehman` | (4n^{1/3} + 2) passes, O(n^{1/3} ln³ n) | 0.33 | 0.36 | ≈ |
| factoring | `pollardRho` | T passes, T ≈ √p (heuristic) | 0.25 | 0.29 | ≈ |
| factoring | `pollardBrent` | 4T steps, T ≈ √p (heuristic) | 0.25 | 0.30 | ≈ |
| factoring | `pollardRhoAcc` | T passes, a gcd per 100 (heuristic) | 0.25 | 0.23 | ≈ |
| factoring | `pollardStrassen (block by block)` | B² ≈ √n products | 0.50 | 0.49 | ≈ |
| factoring | `pollardStrassenFast` | 2^35 n^{1/4} (log₂ n + 3)⁷ (nussModel) | 0.25 | 0.30 | ≈ |
| factoring | `pollardPMinusOne` | π(B) log B modular products | 1.00 | 0.99 | ≈ |
| factoring | `pollardStage2` | O(π(B') log B') products | 1.00 | 0.92 | ≈ |
| discrete logarithms | `bsgs` | O(√p) products and table operations | 0.50 | 0.82 | ▲ |
| discrete logarithms | `rhoLog` | T passes, T ≈ √N (heuristic) | 0.50 | 0.64 | ▲ |

≈ as expected · ▲ grows faster than the bound · ▼ grows slower (e.g. GMP's subquadratic products)

raw timings written to bench/results.csv
(checksum 13592879622958364459)
