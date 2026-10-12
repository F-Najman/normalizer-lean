// Data for T8(b): for Bars's presentations <w,s | w^2, s^h, (ws)^k> at lambda = 5,6,7,
// a finite-index subgroup H with infinite abelianization, and the coset action of w, s.
// Run from ~/normalizer_lean/certs:  magma -b infinite_data.m < /dev/null > infinite_data_output.txt
SetColumns(0);
F<w,s> := FreeGroup(2);
for hk in [[4,4],[8,3],[8,4]] do
  h := hk[1]; k := hk[2];
  G := quo<F | w^2, s^h, (w*s)^k>;
  found := false;
  for H in LowIndexSubgroups(G, 12) do
    inv := AbelianQuotientInvariants(H);
    if 0 in inv then
      f, P := CosetAction(G, H);
      n := Degree(P);
      printf "DATA h=%o k=%o index=%o invariants=%o\n", h, k, n, inv;
      printf "PERM_W %o\n", [ i^f(G.1) : i in [1..n] ];
      printf "PERM_S %o\n", [ i^f(G.2) : i in [1..n] ];
      found := true;
      break;
    end if;
  end for;
  assert found;
end for;
print "DONE";
quit;
