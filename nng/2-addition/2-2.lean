induction c with d hd,
rw add_zero b,
rw add_zero (a + b),
refl,
rw add_succ (a + b),
rw add_succ b,
rw add_succ a,
rw hd,
refl,
