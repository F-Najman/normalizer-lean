// Regular permutation representations of the T8(c,d) presentations (coset 1 = identity).
// Run from ~/normalizer_lean/certs:  magma -b regular_data.m < /dev/null > regular_data_output.txt
SetColumns(0);
F<w,s> := FreeGroup(2);
pres := [* <"c5", quo<F | w^2, s^4, (w*s)^4, (w*s^-1*w*s)^2>>,
           <"c6", quo<F | w^2, s^8, (w*s)^3, (w*s^-1*w*s)^3>>,
           <"d8", quo<F | w^2, s^8, w*s*w*s*w*s^3*w*s^3>> *];
for P in pres do
  G := P[2];
  f, Q := CosetAction(G, sub<G | >);
  n := Degree(Q);
  printf "DATA %o order=%o\n", P[1], n;
  printf "PERM_W %o\n", [ i^f(G.1) : i in [1..n] ];
  printf "PERM_S %o\n", [ i^f(G.2) : i in [1..n] ];
end for;
print "DONE";
quit;
