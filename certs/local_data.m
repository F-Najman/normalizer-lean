// Regular permutation representations of the local presentations of B(p^a) (T5).
// Relators as in localRelList p a (Statements.lean); r = w s^-1 w, [x,y] = x^-1 y^-1 x y.
// Run from ~/normalizer_lean/certs:  magma -b local_data.m < /dev/null > local_data_output.txt
SetColumns(0);
F<w,s> := FreeGroup(2);
br := func< x, y | x^-1*y^-1*x*y >;
r := w*s^-1*w;
u := s^4; v := w*s^4*w;
pres := [* <"L1",  quo<F | w^2, s>>,
           <"L22", quo<F | w^2, s^2, (w*s)^3>>,
           <"L23", quo<F | w^2, s^2, br(r, s)>>,
           <"L24", quo<F | w^2, s^4, (w*s)^3>>,
           <"L25", quo<F | w^2, s^4, br(r^2, s), br(s^2, r), br(r, s)*(r^2*s^2)^-1>>,
           <"L26", quo<F | w^2, s^8, (w*s)^3, br(u, v), s*v*s^-1*(u*v)^-1>>,
           <"L27", quo<F | w^2, s^8, br(r^2, s^2), r^-1*s^2*r*(r^4*s^2)^-1,
                           s^-1*r^2*s*(r^2*s^4)^-1, br(r, s)*(r^6*s^2)^-1>>,
           <"L28", quo<F | w^2, s^8, br(r^2, s), r^-1*s*r*(r^4*s^5)^-1>>,
           <"L29", quo<F | w^2, s^8, br(r, s)>>,
           <"L32", quo<F | w^2, s^3, (w*s)^3>>,
           <"L33", quo<F | w^2, s^3, br(r, s)>> *];
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
