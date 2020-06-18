From mathcomp Require Import all_ssreflect all_algebra all_field.

Section regular.

Import GRing.

Goal forall R : ringType, [the lalgType R of R^o] = R :> ringType.
Proof. by move=> [? []]. Qed.

Goal forall R : comRingType, [the algType R of R^o] = R :> ringType.
Proof. by move=> [? []]. Qed.

Goal forall R : comRingType, [the comAlgType R of R^o] = R :> ringType.
Proof. by move=> [? []]. Qed.

Goal forall R : comUnitRingType, [the unitAlgType R of R^o] = R :> unitRingType.
Proof. by move=> [? []]. Qed.

Goal forall R : comUnitRingType,
    [the comUnitAlgType R of R^o] = R :> comUnitRingType.
Proof. by move=> [? []]. Qed.

Goal forall R : comUnitRingType, [the FalgType R of R^o] = R :> unitRingType.
Proof. by move=> [? []]. Qed.

Goal forall K : fieldType, [the fieldExtType K of K^o] = K :> fieldType.
Proof. by move=> [? []]. Qed.

End regular.
