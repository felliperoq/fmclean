intro p,
induction a with b q,
have r := le_zero (succ 0) p,
apply succ_ne_zero 0,
exact r,
apply q,
apply le_of_succ_le_succ (succ b) b,
exact p,
