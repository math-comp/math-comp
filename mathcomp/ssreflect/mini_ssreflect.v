Require Export mini_ssrbool.
Require Export mini_ssrfun.
Require Export mini_eqtype.
Require Export mini_ssrnat.
Require Export mini_seq.
Require Export mini_div.
Require Export mini_prime.
Require Export mini_path.
Require Export mini_sum.
Module MC.
Module Bool.
Include mini_ssrbool.
End Bool.
Module Nat.
Include mini_ssrnat.
Include mini_div.
Include mini_prime.
Include mini_sum.
End Nat.
Module List.
Include mini_seq.
Include mini_path.
End List.
End MC.
