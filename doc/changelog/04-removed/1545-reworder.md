- in `ssreflect.v`
  + `Global Set SsrOldRewriteGoalsOrder`, for a smooth transition, we recommend adding
    `Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)`
    in each of your files after requiring `ssreflect.v` (even indirectly), which will enable
    porting to the new rewrite subgoals order on a file per file basis
    [note to release managers: this should probably be emphasized in the release notes]
    ([#1545](https://github.com/math-comp/math-comp/pull/1545)).
