ToralElementaryAbelianSubgroups := function(type, p, exp : Isogeny := "SC", Verbose := false)

// to deal with p=2 case
  if p eq 2 then newp := p^2; else newp := p; end if;

if Verbose then "set up Weyl group etc"; end if;
   q := 1;
   repeat q +:= newp; until #PrimeDivisors(q) eq 1;
   GLie := GroupOfLieType(type,q : Isogeny := Isogeny);

   if Isogeny eq "SC" then
      if CartanName(GLie)[1] eq "D" and IsEven(Rank(GLie)) then
         std := DirectSum( HighestWeightRepresentation(GLie,WeightLattice(GLie).(Rank(GLie)-1)),
                           HighestWeightRepresentation(GLie,WeightLattice(GLie).(Rank(GLie))) );
      elif CartanName(GLie)[1] in {"B","D"} then
         std := HighestWeightRepresentation(GLie,WeightLattice(GLie).(Rank(GLie)));
      else
         std  := StandardRepresentation(GLie);
      end if;
   elif Isogeny eq "Ad" then
      std  := AdjointRepresentation(GLie);
   else
       error "(ElementaryAbelianSubgroups) Optional parameter \'Isogeny\' must be one of \"Ad\" or \"SC\".";
   end if;

// W is the 'extended' Weyl group
   V    := sub< Codomain(std) |
                [   elt<GLie | x >@std : x in [1..Rank(GLie)] ] >;
   T    := sub< Codomain(std) | Generators(StandardMaximalTorus(GLie))@std >;
   Tnewp   := sub< Codomain(std) | [t^((q-1) div newp) : t in UserGenerators(T)]>;
   A    := AbelianGroup([ newp : i in [1..Rank(GLie)]]);
   iso  := hom<Tnewp->A | [<UserGenerators(Tnewp)[i],UserGenerators(A)[i]> : i in [1..Rank(GLie)]]>;
   inv  := iso^-1;

// WRed is the actual Weyl group; the quotient of W by its intersection with T
   W     := WeylGroup(GLie);
   Znewp := ResidueClassRing(newp);

// Wnewp is the image of the Weyl group on T_{(newp)}.
// Wp is the image of the Weyl group on T_{(p)}
   VtoWnewp := hom< V -> GL(Rank(GLie),Znewp) |
                    x :-> GL(Rank(GLie),Znewp)!&cat[Eltseq((i^x)@iso) : i in UserGenerators(Tnewp)]>;
   Wnewp    := sub< GL(Rank(GLie),Znewp) | [VtoWnewp(i):i in UserGenerators(V)]>;
   VtoWp    := hom< V -> GL(Rank(GLie),p) |
                    x :-> GL(Rank(GLie),p)!&cat[Eltseq((i^x)@iso) : i in UserGenerators(Tnewp)]>;
   Wp       := sub< GL(Rank(GLie),p) | [VtoWp(i):i in UserGenerators(V)]>;

if Verbose then "compute W-classes of order p elements"; end if;
   orbs := [i : i in Orbits(Wnewp) | forall(j){j : j in i | p*j eq 0*j}
                                     and not (#i eq 1 and i[1] eq 0*i[1])];
   cl   := [i[1] : i in orbs];

   //identify class of elts
   classMap := AssociativeArray();
   for i in [1..#orbs] do for x in orbs[i] do classMap[x] := i; end for; end for;
   class    := func<x | IsDefined(classMap, x) select classMap[x] else false>;

if Verbose then "compute W-classes of subgroups"; end if;
   Snewp   := Parent(orbs[1][1]);
   orb_raw := OrbitsOfSpaces(Wp,exp);
   orb_Vp  := [i[2] : i in orb_raw];
   orb     := [
      <i[1],sub<Snewp | [((p eq 2) select 2 else 1)*y
        : y in [Snewp![Integers()!u : u in Eltseq(e)] : e in Basis(i[2])]]>>
      : i in orb_raw
   ];

   NW   := [Stabiliser(Wnewp,i[2]) : i in orb];
   CW   := [];
   for i in [1..#orb] do
      Y := NW[i];
      for t in Basis(orb[i][2]) do Y := Stabiliser(Y,t); end for;
      Append(~CW,Y);
   end for;

if Verbose then "determine types of subgroups"; end if;
   findDist := func<x| [  Multiplicity({* class(j) : j in [v : v in x | not v eq 0*v] *},i)
                          : i in [1..#orbs]]>;
   types    := [findDist(O[2]) : O in orb];

if Verbose then "start centraliser"; end if;
if Verbose then "centrts"; end if;
// x_r(1) centralises torus element with coord a iff Roots(D)[r] * CartanMatrix * a = 0 mod newp
   D      := RootDatum(GLie);
   CmatZn := ChangeRing(CartanMatrix(D), Znewp);
   NallCn := Matrix(Znewp, [[Znewp!c : c in Eltseq(Roots(D)[r])] : r in [1..#Roots(GLie)]]) * CmatZn;
   coordmats := [ Matrix(Znewp, #Basis(orb[k][2]), Rank(GLie),
                         &cat[Eltseq(v) : v in Basis(orb[k][2])])
                : k in [1..#orb] ];
   centrts := [];
   for k in [1..#orb] do
       M := NallCn * Transpose(coordmats[k]);
       Append(~centrts, { r : r in [1..#Roots(GLie)] | IsZero(M[r]) });
   end for;

if Verbose then "sizePTorsCent"; end if;
// The number of p-torsion torus elements centralising a subspace with root set centrts_X
// equals p^(rk - Rank(Np * Cp)), where Np has rows = root coords mod p and Cp = CartanMatrix
// mod p. This is uniform in p: for p=2 (newp=4) the p-torsion of the T_(4) kernel bijects
// to the GF(2) kernel of N*Cmat mod 2, giving the same formula.
   Cp := ChangeRing(CartanMatrix(D), GF(p));
   sizePTorsCent := [];
   for i in [1..#orb] do
       if #centrts[i] eq 0 then
           Append(~sizePTorsCent, p^Rank(GLie));
       else
           Np := Matrix(GF(p), [ [GF(p)!c : c in Eltseq(Roots(D)[r])] : r in centrts[i] ]);
           Append(~sizePTorsCent, p^(Rank(GLie) - Rank(Np * Cp)));
       end if;
   end for;

if Verbose then "compute IsMaximal"; end if;
   isMaximal := [];
   for i in [1..#orb] do
      if sizePTorsCent[i] eq p^exp then
         Vp_i   := orb_Vp[i];
         H_i    := Stabiliser(Wp, Vp_i);
         n      := exp;
         B      := Basis(Vp_i);
         M_gens := [];
         for g in Generators(H_i) do
            rows := [Coordinates(Vp_i, B[j] * g) : j in [1..n]];
            Append(~M_gens, Matrix(GF(p), n, n, rows));
         end for;
         H_mat := sub<GL(n, GF(p)) | M_gens>;
         Mod_i := GModule(H_mat);
         if IsIrreducible(Mod_i) then
            Append(~isMaximal, true); // If N_G(E) =: H_i is irreducible then E = Vp_i admits no
                                      // witnesses to N_G(E) < N_G(Y), hence H_i is maximal p-local
         else
            // At this point, E has N_G(E) =: H_i-stable subgroups but these might not preclude
            // N_G(E) being maximal p-local; we need to check whether these subgroups are also
            // in ERp(G); test this using tNewpCent as above. If yes, then Lemma `lempl` (as applied
            // in Remark `rk:toralmax`) tells us that, since Y < E (strict), we have N_G(E) < N_G(Y)
            // (strict), and therefore N_G(E) is not maximal-proper p-local. If no (for all Y),
            // then there are no witnesses and N_G(E) is maximal-proper p-local.
            subs_i       := Submodules(Mod_i);
            foundWitness := false;
            for S in subs_i do
               d := Dimension(S);
               if d gt 0 and d lt n then
                  Emb      := Morphism(S, Mod_i);
                  Ysub_pts := [ &+[ v[j]*B[j] : j in [1..n] ] : v in Rows(Emb) ];
                  Ysub     := sub< Vp_i | Ysub_pts >;

                  Ysub_lift := sub<Snewp | [((p eq 2) select 2 else 1)*y
                                 : y in [Snewp![Integers()!u : u in Eltseq(e)]
                                         : e in Basis(Ysub)]]>;
                  coordmat_Y := Matrix(Znewp, #Basis(Ysub_lift), Rank(GLie),
                                       &cat[Eltseq(v) : v in Basis(Ysub_lift)]);
                  M_Y       := NallCn * Transpose(coordmat_Y);
                  centrts_Y := { r : r in [1..#Roots(GLie)] | IsZero(M_Y[r]) };
                  if #centrts_Y eq 0 then
                      sizePTorsCent_Y := p^Rank(GLie);
                  else
                      Np_Y := Matrix(GF(p), [ [GF(p)!c : c in Eltseq(Roots(D)[r])] : r in centrts_Y ]);
                      sizePTorsCent_Y := p^(Rank(GLie) - Rank(Np_Y * Cp));
                  end if;

                  if sizePTorsCent_Y eq p^d then
                     foundWitness := true;
                     break;
                  end if;
               end if;
            end for;
            Append(~isMaximal, not foundWitness);
         end if;
      else
         Append(~isMaximal, false);
      end if;
   end for;

if Verbose then "weylsubgens"; end if;
   weylsubgens := [   [   std(elt< GLie | [<i,1>,<i in [1..#PositiveRoots(GLie)]
                          select i+#PositiveRoots(GLie)
                          else i-#PositiveRoots(GLie),-1>,<i,1>]>)
                        : i in centrts[k] ]
                    : k in [1..#orb] ];

if Verbose then "weylsubs"; end if;
   weylsubs := [   sub< Wnewp | [  GL(Rank(GLie),Znewp)!&cat[Eltseq((i^w)@iso) : i in UserGenerators(Tnewp)]
                               : w in weylsubgens[k]] >
                : k in [1..#orb] ];

if Verbose then "cents"; end if;
   cents    := [ sub< D | centrts[k] > : k in [1..#orb] ];

if Verbose then "compute outer quotient"; end if;
   new := [];
   for i in [1..#orb] do new[i] := quo<NW[i]|CW[i]>; end for;
   NW  := new;


if Verbose then "computes component group of centraliser"; end if;
   for i in [1..#orb] do new[i] := quo<CW[i] | CW[i] meet weylsubs[i]>; end for;
   CW := new;

if Verbose then "output results"; end if;
   res := [**];
   for i in [1..#orb] do Append(~res, [*types[i], cents[i], CW[i], NW[i], sizePTorsCent[i], isMaximal[i] *]); end for;

if Verbose then
   "type -- connected cent -- component grp cent -- out -- IsERp -- IsMaximal";
   [ < i[1], CartanName(i[2]), #i[3], #i[4], i[5] eq p^exp, i[6] > : i in res];
end if;

   return res;

end function;

/*
   This code has been extended relative to the GitHub-published version in two ways:

   (1) IsERp: indicated whether E lies in ERp(G), i.e. E = Omega_1(Z(O_p(N_G(E)))). This is detected
       by checking whether sizePTorsCent = p^exp, where sizePTorsCent = p^(rk - Rank(Np * Cp)) with
       Np having rows = root coords mod p and Cp = CartanMatrix mod p. This formula counts p-torsion
       torus elements centralising C_G(E)^circ uniformly for all p: for p=2 (newp=4) the p-torsion
       of the T_(4) kernel bijects to the GF(2) kernel of N*Cmat mod 2.

   (2) IsMaximal: a boolean flag indicating whether N_G(E) is a proper-maximal p-local subgroup of G
       (for toral E in ERp(G)). This is calculating using a deterministic search for witnesses to
       its failure: If N_G(E) is irreducible, or if it is reducible but all N_G(E)-stable subgroups
       fail to lie in ERp(G), then no such witnesses exist. On the other hand, if there is an
       N_G(E)-stable subgroup Y of E in ERp(G), then Lemma `lempl` (as applied in Remark
       `rk:toralmax`) tells us that N_G(E) < N_G(Y).
*/
