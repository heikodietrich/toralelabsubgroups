ToralElementaryAbelianSubgroups := function(type, p, exp : Isogeny := "SC")

// to deal with p=2 case
  if p eq 2 then newp := p^2; else newp := p; end if;

"set up Weyl group etc"; 
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
   
"compute W-classes of order p elements";
   orbs := [i : i in Orbits(Wnewp) | forall(j){j : j in i | p*j eq 0*j}
                                     and not (#i eq 1 and i[1] eq 0*i[1])];
   cl   := [i[1] : i in orbs]; 

   //identify class of elts
   class     := func<x | exists(i){i : i in [1..#cl] | x in orbs[i]} select i else false>;

"compute W-classes of subgroups";
   Snewp := Parent(orbs[1][1]);
   orb   := OrbitsOfSpaces(Wp,exp);
   new   := [];
   for i in orb do
      Append(~new,
       <i[1],sub<Snewp | [((p eq 2) select 2 else 1)*y
                          : y in [Snewp![Integers()!u : u in Eltseq(e)] : e in Basis(i[2])]]>>);
   end for;
   orb := new;

   NW   := [Stabiliser(Wnewp,i[2]) : i in orb];
   CW   := [];
   for i in [1..#orb] do
      Y := NW[i];
      for t in Basis(orb[i][2]) do Y := Stabiliser(Y,t); end for;
      Append(~CW,Y);
   end for;

"determine types of subgroups";
   findDist := func<x| [  Multiplicity({* class(j) : j in [v : v in x | not v eq 0*v] *},i)
                          : i in [1..#orbs]]>;
   types    := [findDist(O[2]) : O in orb];

"start centraliser";
"genset";
   genset  := [ [ inv(i) : i in [A!Eltseq(j) : j in Basis(v[2])] ] : v in orb];  

"centrts";
   centrts := [   { i : i in [1..#Roots(GLie)] | 
                    forall(t){t: t in genset[k] | 
                              ELT*t eq t*ELT} where ELT := std(elt< GLie | [<i,1>]>)}
                : k in [1..#orb] ];

"weylsubgens";
   weylsubgens := [   [   std(elt< GLie | [<i,1>,<i in [1..#PositiveRoots(GLie)] 
                          select i+#PositiveRoots(GLie) 
                          else i-#PositiveRoots(GLie),-1>,<i,1>]>) 
                        : i in centrts[k] ] 
                    : k in [1..#orb] ];

"weylsubs";
   weylsubs := [    sub< Wnewp | [  GL(Rank(GLie),Znewp)!&cat[Eltseq((i^w)@iso) : i in UserGenerators(Tnewp)] 
                                : w in ww] > 
                 : ww in weylsubgens];

"cents";
   cents    := [ sub< RootDatum(GLie) | centrts[k] > : k in [1..#orb] ];

"compute outer quotient";
   new := [];
   for i in [1..#orb] do new[i] := quo<NW[i]|CW[i]>; end for;
   NW  := new;


"computes component group of centraliser";
   for i in [1..#orb] do new[i] := quo<CW[i]|weylsubs[i]>; end for;
   CW := new;

"output results";
   res := [**];
   for i in [1..#orb] do Append(~res, [*types[i], cents[i], CW[i], NW[i] *]); end for;

"type -- connected cent -- component grp cent -- out";
   [ < i[1], CartanName(i[2]), #i[3], #i[4]> : i in res];;

   return res;

end function;



