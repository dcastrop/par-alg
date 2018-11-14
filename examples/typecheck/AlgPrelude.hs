module AlgPrelude where

data Pair2 a b
    = Pair2 a b
proj0_2 (Pair2 a b) = a
proj1_2 (Pair2 a b) = b
data Pair3 a b c
    = Pair3 a b c
proj0_3 (Pair3 a b c) = a
proj1_3 (Pair3 a b c) = b
proj2_3 (Pair3 a b c) = c
data Pair4 a b c d
    = Pair4 a b c d
proj0_4 (Pair4 a b c d) = a
proj1_4 (Pair4 a b c d) = b
proj2_4 (Pair4 a b c d) = c
proj3_4 (Pair4 a b c d) = d
data Pair5 a b c d e
    = Pair5 a b c d e
proj0_5 (Pair5 a b c d e) = a
proj1_5 (Pair5 a b c d e) = b
proj2_5 (Pair5 a b c d e) = c
proj3_5 (Pair5 a b c d e) = d
proj4_5 (Pair5 a b c d e) = e
data Sum2 a b
    = Inj0_2 a
    | Inj1_2 b
data Sum3 a b c
    = Inj0_3 a
    | Inj1_3 b
    | Inj2_3 c
data Sum4 a b c d
    = Inj0_4 a
    | Inj1_4 b
    | Inj2_4 c
    | Inj3_4 d
data Sum5 a b c d e
    = Inj0_5 a
    | Inj1_5 b
    | Inj2_5 c
    | Inj3_5 d
    | Inj4_5 e
