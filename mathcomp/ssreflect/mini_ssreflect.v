Require Export mini_ssrbool.
Require Export mini_ssrfun.
Require Export mini_eqtype.
Require Export mini_ssrnat.
Require Export mini_seq.
Require Export mini_div.
Module MC.
Module Bool.
Include mini_ssrbool.
End Bool.
Module Nat.
Include mini_ssrnat.
Include mini_div.
End Nat.
Module List.
Include mini_seq.
End List.
End MC.
