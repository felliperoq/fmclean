revert a,
induction b with c d,
intro a,
right,
exact zero_le a,
intro b,
cases b with j k,
left,
exact zero_le (succ c),
cases d j,
left,
apply succ_le_succ j c,
exact h,
right,
apply succ_le_succ c j,
exact h, 
