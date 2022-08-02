From mathcomp Require Import all_ssreflect ssralg.

Section Tests.
Lemma test_orb (a b c d : bool) : (a || b) || (c || d) = (a || c) || (b || d).
Proof. time by rewrite orbACA. Abort.
Lemma test_orb (a b c d : bool) : (a || b) || (c || d) = (a || c) || (b || d).
Proof. time by rewrite (AC (2*2) ((1*3)*(2*4))). Abort.
Lemma test_orb (a b c d : bool) : (a || b) || (c || d) = (a || c) || (b || d).
Proof. time by rewrite orb.[AC (2*2) ((1*3)*(2*4))]. Qed.

Lemma test_addn (a b c d : nat) : a + b + c + d = a + c + b + d.
Proof. time by rewrite -addnA addnAC addnA addnAC. Abort.
Lemma test_addn (a b c d : nat) : a + b + c + d = a + c + b + d.
Proof. time by rewrite (ACl (1*3*2*4)). Abort.
Lemma test_addn (a b c d : nat) : a + b + c + d = a + c + b + d.
Proof. time by rewrite addn.[ACl 1*3*2*4]. Qed.

Lemma test_addr (R : comRingType) (a b c d : R) : (a + b + c + d = a + c + b + d)%R.
Proof. time by rewrite -GRing.addrA GRing.addrAC GRing.addrA GRing.addrAC. Abort.
Lemma test_addr (R : comRingType) (a b c d : R) : (a + b + c + d = a + c + b + d)%R.
Proof. time by rewrite (ACl (1*3*2*4)). Abort.
Lemma test_addr (R : comRingType) (a b c d : R) : (a + b + c + d = a + c + b + d)%R.
Proof. time by rewrite (@GRing.add R).[ACl 1*3*2*4]. Qed.

Local Open Scope ring_scope.
Import GRing.Theory.

Lemma test_mulr (R : comRingType) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : R)
    (x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : R) :
    (x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) *
    (x10 * x11) * (x12 * x13) * (x14 * x15) * (x16 * x17 * x18 * x19) *
 (x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) *
    (x10 * x11) * (x12 * x13) * (x14 * x15) * (x16 * x17 * x18 * x19) =
    (x0 * x2 * x4 * x9) * (x1 * x3 * x5 * x7) * x6 * x8 *
    (x10 * x12 * x14 * x19) * (x11 * x13 * x15 * x17) * x16 * x18 * (x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) *
    (x10 * x11) * (x12 * x13) * (x14 * x15) * (x16 * x17 * x18 * x19)
   *(x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) *
    (x10 * x11) * (x12 * x13) * (x14 * x15) * (x16 * x17 * x18 * x19) *
 (x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) *(x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) *
    (x10 * x11) * (x12 * x13) * (x14 * x15) * (x16 * x17 * x18 * x19) *
 (x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) * (x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) *
    (x10 * x11) * (x12 * x13) * (x14 * x15) * (x16 * x17 * x18 * x19)
   *(x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) *
    (x10 * x11) * (x12 * x13) * (x14 * x15) * (x16 * x17 * x18 * x19) *
 (x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) *(x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) *
    (x10 * x11) * (x12 * x13) * (x14 * x15) * (x16 * x17 * x18 * x19) *
 (x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) * (x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) *
    (x10 * x11) * (x12 * x13) * (x14 * x15) * (x16 * x17 * x18 * x19)
   *(x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) *
    (x10 * x11) * (x12 * x13) * (x14 * x15) * (x16 * x17 * x18 * x19) *
 (x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) *(x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) *
    (x10 * x11) * (x12 * x13) * (x14 * x15) * (x16 * x17 * x18 * x19) *
 (x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) *
    (x10 * x11) * (x12 * x13) * (x14 * x15) * (x16 * x17 * x18 * x19) *
 (x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) * (x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) *
    (x10 * x11) * (x12 * x13) * (x14 * x15) * (x16 * x17 * x18 * x19)
   *(x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) *
    (x10 * x11) * (x12 * x13) * (x14 * x15) * (x16 * x17 * x18 * x19) *
 (x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) *(x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) *
    (x10 * x11) * (x12 * x13) * (x14 * x15) * (x16 * x17 * x18 * x19) *
 (x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) * (x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) *
    (x10 * x11) * (x12 * x13) * (x14 * x15) * (x16 * x17 * x18 * x19)
   *(x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) *
    (x10 * x11) * (x12 * x13) * (x14 * x15) * (x16 * x17 * x18 * x19) *
 (x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) *(x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) *
    (x10 * x11) * (x12 * x13) * (x14 * x15) * (x16 * x17 * x18 * x19) *
 (x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9)*
    (x10 * x11) * (x12 * x13) * (x14 * x15) * (x16 * x17 * x18 * x19) *
 (x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) * (x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) *
    (x10 * x11) * (x12 * x13) * (x14 * x15) * (x16 * x17 * x18 * x19)
   *(x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) *
    (x10 * x11) * (x12 * x13) * (x14 * x15) * (x16 * x17 * x18 * x19) *
 (x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) *(x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) *
    (x10 * x11) * (x12 * x13) * (x14 * x15) * (x16 * x17 * x18 * x19) *
 (x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) * (x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) *
    (x10 * x11) * (x12 * x13) * (x14 * x15) * (x16 * x17 * x18 * x19)
   *(x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) *
    (x10 * x11) * (x12 * x13) * (x14 * x15) * (x16 * x17 * x18 * x19) *
 (x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) *(x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) *
    (x10 * x11) * (x12 * x13) * (x14 * x15) * (x16 * x17 * x18 * x19) *
 (x0 * x1) * (x2 * x3) * (x4 * x5) * (x6 * x7 * x8 * x9) .
Proof.
pose s := ((2 * 4 * 9 * 1 * 3 * 5 * 7 * 6 * 8 * 20 * 21 * 22 * 23) * 25 * 26 * 27 * 28
             * (29 * 30 * 31) * 32 * 33 * 34 * 35 * 36 * 37 *  38 * 39 * 40 * 41
             * (10 * 12 * 14 * 19 * 11 * 13 * 15 * 17 * 16 * 18 * 24)
                  * (42 * 43 * 44 * 45 * 46 * 47 *  48 * 49) * 50
                  * 52 * 53 * 54 * 55 * 56 * 57 *  58 * 59 * 51* 60
                  * 62 * 63 * 64 * 65 * 66 * 67 *  68 * 69 * 61* 70
                  * 72 * 73 * 74 * 75 * 76 * 77 *  78 * 79 * 71 * 80
                  * 82 * 83 * 84 * 85 * 86 * 87 *  88 * 89 * 81* 90
                  * 92 * 93 * 94 * 95 * 96 * 97 *  98 * 99 * 91 * 100 *
((102 * 104 * 109 * 101 * 103 * 105 * 107 * 106 * 108 * 120 * 121 * 122 * 123) * 125 * 126 * 127 * 128
             * (129 * 130 * 131) * 132 * 133 * 134 * 135 * 136 * 137 *  138 * 139 * 140 * 141
             * (110 * 112 * 114 * 119 * 111 * 113 * 115 * 117 * 116 * 118 * 124)
                  * (142 * 143 * 144 * 145 * 146 * 147 *  148 * 149) * 150
                  * 152 * 153 * 154 * 155 * 156 * 157 *  158 * 159 * 151* 160
                  * 162 * 163 * 164 * 165 * 166 * 167 *  168 * 169 * 161* 170
                  * 172 * 173 * 174 * 175 * 176 * 177 *  178 * 179 * 171 * 180
                  * 182 * 183 * 184 * 185 * 186 * 187 *  188 * 189 * 181* 190
                  * 192 * 193 * 194 * 195 * 196 * 197 *  198 * 199 * 191)

)%AC.
time have := (@GRing.mul R).[ACl s].
time rewrite (@GRing.mul R).[ACl s].
Abort.
End Tests.
