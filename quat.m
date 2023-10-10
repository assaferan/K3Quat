// !!!  this file is a slight modification of Voight's original
// implementation in Magma fo constructing a quaternion algebra with prescribed ramification
// Main difference is simply the main loop in the probabilistic method.

freeze;

// exports :
// intrinsic MyQuaternionAlgebra(I::RngOrdIdl,S::SeqEnum[PlcNumElt] :
//			      Optimized := true) -> AlgQuat

// This algorithm implements [Voight, Algorithm 4.3.7], corrected: 
// It finds a solution to the equation 
//   x^2 - ay^2 - bz^2 + abw^2 = 0 (mod 4)
// with x = 1 (mod 4) if Valuation(a) = 0 and Valuation(b) = 1.
function EvenDiagonalNormForm(a,b)
  K := Parent(a);
  O := Integers(K);
  p := Prime(K);

  e := RamificationIndex(K);
  
  pi := UniformizingElement(O);
  k, fk := ResidueClassField(O);
  f := Degree(k);

  assert Valuation(a) eq 0 and Valuation(b) eq 1;

  // Eltseq gives coefficients in terms of O.1, which may or may not be a
  // uniformizer!
  function EltseqUniformizerFull(x, l)
    x0 := x;
    xseq := [];
    for i := 1 to l do
      x0k := fk(x0);
      xseq cat:= Eltseq(x0k);
      x0 := (x0-(x0k@@fk))/pi;
    end for;
    return xseq;
  end function;

/*
  // Master vector upon which we record coefficients.
  V := [((k.1^i)@@fk)*pi^j : i in [0..f-1], j in [0..e-1]];

  // Compute the kernel of the augmented norm map.
  M := Matrix(k, [ EltseqUniformizerFull(c*v^2,e) : v in V, c in [1,-a,-b,a*b]]);
  Mker := Kernel(M);
  // Basis will be echelonized, so the first row vector will have the earliest
  // nonzero term
  v0 := [ &+[V[i]*((Mker.1)[i+f*e*(j-1)]@@fk) : i in [1..#V]] : j in [1..4]];
  if fk(v0[1]) eq 0 then
    // Fatal error has occurred; could be due to improper input, we need 
    // a to be not divisible by p.
    error "Fatal error in 'EvenDiagonalNormForm': "
         *"Failed to find proper element in kernel (1)";
  end if;
*/

  v0 := [1, (1/Sqrt(fk(a)))@@fk, 0, 0];
  Nv0 := v0[1]^2-a*v0[2]^2-b*v0[3]^2+a*b*v0[4]^2;

  procedure PseudoHenselLift(~v0,~Nv0)
    valNv0 := Valuation(Nv0);
    if valNv0 mod 2 eq 0 then
      v0[1] +:= (Sqrt(fk(-Nv0/pi^valNv0))@@fk)*pi^(valNv0 div 2);
    else
      v0[3] +:= (Sqrt(fk(Nv0/(b*pi^(valNv0-1))))@@fk)*pi^(valNv0 div 2);
    end if;
    Nv0 := v0[1]^2-a*v0[2]^2-b*v0[3]^2+a*b*v0[4]^2;
  end procedure;

  while Valuation(Nv0) lt 2*e do
    PseudoHenselLift(~v0,~Nv0);
  end while;

  return [1,v0[2]/v0[1],v0[3]/v0[1],0];
end function;

// Evaluates the Hilbert symbol for p an even prime
function EvenHilbertSymbol(A,p)
  // Remember for return alpha, beta
  _, _, Astan, phi := StandardForm(A);
  alpha := Astan.1@@phi;
  beta := Astan.2@@phi;
  a := Norm(alpha);
  b := Norm(beta);

  F := BaseField(A);
  Z_F := MaximalOrder(F);
  prec_extra := Max(Abs(Valuation(a, p)), Abs(Valuation(b, p)));
  Fp, mFp := Completion(F,p : Precision := 20+prec_extra);
  Op := Integers(Fp);
  k, fk := ResidueClassField(Op);

  ap := -mFp(a);
  bp := -mFp(b);
  e := RamificationIndex(Fp);

  // Normalize valuations of elements: a has valuation 0, 
  // b has valuation 1
  piFp := SafeUniformiser(p);
  pi := mFp(piFp);

  facts := Decomposition(Z_F,2);
  I := [q[1] : q in facts | q[1] ne p];
  V := [0 : i in I];
  piinvFp := WeakApproximation([p] cat I, [-1] cat V);

  // Step one: Ensure a,b have valuations in {0,1}  
  vala := Valuation(ap) div 2;
  valb := Valuation(bp) div 2;
  ap /:= pi^(2*vala);
  alpha /:= piFp^vala;
  bp /:= pi^(2*valb);
  beta /:= piFp^valb;

  if Valuation(ap) eq 1 then
    if Valuation(bp) eq 1 then
      ap := -ap*bp/pi^2;
      alpha := alpha*beta/piFp;
    else
      cp := ap;
      ap := bp;
      bp := cp;
      gamma := alpha;
      alpha := beta;
      beta := gamma;
    end if;
  end if;

  if Valuation(bp) eq 1 then
    xiseq := EvenDiagonalNormForm(ap,bp);
  else
    // Eltseq gives coefficients in terms of O.1, which may or may not be a 
    // uniformizer!
    function EltseqUniformizer(x, l)
      x0 := x;
      xseq := [];
      for i := 1 to l do
        Append(~xseq, fk(x0));
        x0 := (x0-(xseq[#xseq]@@fk))/pi;
      end for;
      return xseq;
    end function;

    apseq := EltseqUniformizer(ap,e);
    bpseq := EltseqUniformizer(bp,e);
    M := Matrix([apseq, bpseq]);
    M0 := ColumnSubmatrix(M, [i : i in [1..e] | i mod 2 eq 0]);

    if Rank(M0) eq 0 then
      a0 := &+[Sqrt(apseq[i])@@fk*pi^(i div 2) : i in [i: i in [1..e] | i mod 2 eq 1]];
      b0 := &+[Sqrt(bpseq[i])@@fk*pi^(i div 2) : i in [i: i in [1..e] | i mod 2 eq 1]];
      xiseq := [1,1/a0,1/b0,1/(a0*b0)];
    else
      if IsZero(M0[1]) then
        alpha0 := beta;
        beta0 := alpha;
        alpha := alpha0;
        beta := beta0;
        ap := -mFp(Norm(alpha));
        bp := -mFp(Norm(beta));
        apseq := EltseqUniformizer(ap,e);
        bpseq := EltseqUniformizer(bp,e);
        SwapRows(~M0, 1, 2);
      end if;

      tf2 := 1;
      while M0[1][tf2] eq 0 do
        tf2 +:= 1;
      end while;
      tf2 -:= 1;

      a0 := &+[Sqrt(apseq[i])@@fk*pi^(i div 2) : i in [i: i in [1..2*(tf2+1)] | i mod 2 eq 1]];
      at := (ap - a0^2)/pi^(2*tf2+1);

      xiseq_re := EvenDiagonalNormForm(ap,-pi*at/bp);
      y := xiseq_re[2];
      z := xiseq_re[3];
      xiseq := [1, 1/a0, pi^tf2/(a0*z), pi^tf2*y/(a0*z)];
    end if;

    xiseqlift := [c@@mFp : c in xiseq];
    xi := xiseqlift[1] + xiseqlift[2]*alpha + xiseqlift[3]*beta + xiseqlift[4]*alpha*beta;
    assert Valuation(mFp(Norm(xi))) ge Valuation(mFp(4));
  end if;

  xiseqlift := [xiseq[i]@@mFp : i in [1..4]];
  ZFmod8, m8 := quo<Z_F | 8>;

  // Coefficients only matter modulo 8, so reduce them to this size.
  OddDenominator := function(a);
    den := Denominator(a);
    while den mod 2 eq 0 do
      den div:= 2;
    end while;
    return den;
  end function;

  alpha *:= OddDenominator(Norm(alpha));
  beta *:= OddDenominator(Norm(beta));

  xiseqlift := [m8(xiseq[i]@@mFp)@@m8 : i in [1..4]];

  for i := 1 to 4 do
    // Small hack to reduce the sizes of the coefficients of xi,
    // not necessary, but nice anyway.
    if Max([Numerator(x) : x in Eltseq((-xiseq[i])@@mFp)]) lt 
       Max([Numerator(x) : x in Eltseq(xiseqlift[i])]) then
      xiseqlift[i] := -((-xiseq[i])@@mFp);
    end if;
  end for;

  xiseq := xiseqlift;
  xi := xiseq[1] + xiseq[2]*alpha + xiseq[3]*beta + xiseq[4]*alpha*beta;
  xi *:= piinvFp^e;

  // By Hensel's lemma, the characteristic polynomial of alpha
  //   x^2 - x + nrd(alpha)
  // has a root in K if and only if it has a root modulo p.

  Nxi := Norm(xi);
  trxi := Trace(xi);
  zeta := QuaternionicComplement(xi);
  z := Norm(zeta);
  valz := Valuation(mFp(z)) div 2;
  zeta *:= piinvFp^valz;

  if #Roots(PolynomialRing(k) ! [fk(mFp(Nxi)),-fk(mFp(trxi)),1]) ge 1 then
    return 1, xi, zeta;
  else
    // K(alpha) is an unramified extension of K, so by [Vigneras, Theoreme
    // II.1.3], it is a division ring if and only if the complementary element 
    // is a uniformizer.

    if Valuation(mFp(Norm(zeta))) eq 0 then
      return 1, xi, zeta;
    else
      return -1, xi, zeta;
    end if;
  end if;
end function;

function MyTameOrder(A)

  F := BaseField(A);

  // This might be an expensive step, but is necessary.
  // (And it should need to be only called once per F!)
  Z_F := MaximalOrder(F);

  // Correction factor for even primes
  dOfact := Factorization(ideal<Z_F | 1/4>);
  dO := ideal<Z_F | 1>;

  S := [];
  I := [];
  dKfacts := [];

  _, _, Astandard, phi := StandardForm(A);
  As := [Astandard.i@@phi : i in [1..3]];
  for i := 1 to 3 do
    // Force integrality
    alpha := As[i];
    alpha *:= Denominator(Norm(alpha));
 
    f := MinimalPolynomial(alpha);
    if not IsIrreducible(f) then
      // alpha yields a zerodivisor
      alphabar := Roots(f)[1][1];
      vprintf K3Quat,3: "alpha = %o, f = %o\n", alpha, f;
      M2F, phi := MatrixRing(A, alpha-alphabar);

      // Hard-coded matrix units; these generate the maximal order M_2(Z_F)
      mU := [Inverse(phi)(M2F.i) : i in [1..2]];
      O := Order(mU);
      O`Discriminant := ideal<Z_F | 1>;
      O`FactoredDiscriminant := []; 
      return O;
    end if;

    // We actually only want a maximal order away from 2, and want
    // the order generated by alpha at 2.  We also want to remember
    // the factorization of the discriminant of K.  So it seems best
    // to work directly, prime by prime.
    O_K := ext<Z_F | MinimalPolynomial(alpha)>;
    K := FieldOfFractions(O_K);
    dK := Z_F !! Discriminant(O_K);

    // The following should be the most expensive step.  But according 
    // to [Voight], computing maximal orders is probablistic 
    // polynomial-time equivalent to factorization, so it has to be done!
    vprintf K3Quat, 1 : "Factoring discriminant %o...", dK;
    dKfact := Factorization(dK);
    vprintf K3Quat, 1 : "Done!\n";
    dKfactnew := [];
    for pp in dKfact do
      if AbsoluteNorm(pp[1]) mod 2 ne 0 then
        if pp[2] gt 1 then
          O_K := pMaximalOrder(O_K, pp[1]);
        end if;
        if pp[2] mod 2 eq 1 then
          Append(~dKfactnew, <pp[1],1>);
        end if;
      else
        // We ignore even primes.  (Adding 2-integral elements may not
        // even return an order!)
        Append(~dKfactnew, pp);
      end if;
    end for;

    // Now combine the factorizations of dKfactnew and dOfact.
    // Would be nice to do dOfact *:= dKfactnew, like we can for integers...
    for pp in dKfactnew do
      blfound := false;
      for j := 1 to #dOfact do
        if dOfact[j][1] eq pp[1] then
          dOfact[j][2] +:= pp[2];
          blfound := true;
          break j;
        end if;
      end for;
      if not blfound then
        Append(~dOfact, pp);
      end if;
    end for; 

    // Store the new generator as an element of the quaternion algebra,
    // and store the coefficient ideal
    // Assumes (correctly for now anyway) that the pseudobases of the 
    // modules O_K have 1 as their first generator.
    S[i] := Eltseq(K ! O_K.2)[2]*alpha;
    I[i] := PseudoBasis(Module(O_K))[2][1];
    dKfacts[i] := dKfactnew;
  end for;

  sortFact := function(pp,qq);
    p := Generator(pp[1] meet Integers());
    q := Generator(qq[1] meet Integers());
    if p lt q then
      return -1;
    elif p gt q then
      return 1;
    else
      return 0;
    end if;
  end function;

  O := Order(S, I);
  O`FactoredDiscriminant := Sort([<pp[1], pp[2] div 2> : pp in dOfact], sortFact); 
  O`Discriminant := &*[ pp[1]^pp[2] : pp in O`FactoredDiscriminant];
  dKs := [ &*[ pp[1]^pp[2] : pp in dKfacts[i] ] : i in [1..3]];
  O`TraceZeroInternalData := <S, I, dKs>;
  return O;
end function;

// Computes a pp-maximal order for pp an even prime.
function pEvenMaximalOrder(O,pp);
  Oold := O;
  A := Algebra(O);

  // The output of EvenHilbertSymbol includes an element xi such that
  // Z_F[xi] has discriminant not divisible by pp.

  k, mk := ResidueClassField(pp);
  h, xi := EvenHilbertSymbol(A, pp);
  if h eq -1 and Valuation(Discriminant(O),pp) eq 1 then
    return O;
  end if;

  J := ideal<O | [xi-1] cat Generators(pp)>;
  O := RightOrder(J);
 
  // Compute a tame pp-order containing O by finding linear combinations of 
  // the two elements zeta which have norm with valuation >= 2 at pp.
  piinvFp := SafeInverseUniformiser(pp);
  repeat
    // Find elements zeta in O which are locally linearly independent 
    // generators for O and have trace zero (hence orthogonal to xi).
    B := TraceZeroSubspace(O);
    zetas := [ [gi*(A ! B[i][2]) : gi in Generators(B[i][1]) ] : i in [1..3] ];
    for i in [1..3] do
      _, t := Min([Valuation(Norm(z), pp) : z in zetas[i]]);
      zetas[i] := [zetas[i][t]];
    end for;
    zetas := &cat(zetas);
    T := [Valuation(Norm(z), pp) : z in zetas];
    mt, t := Max(T);

    vprintf K3Quat, 3 :  "valuation = %o, T = %o\n",
			 Valuation(Discriminant(O), pp), T;
    if zetas[t] in ideal<O | Generators(pp)> then
      J := ideal<O | [zetas[t]*piinvFp] cat Generators(pp)>;
    else
      if mt le 1 then
        // Just normalize the quadratic form to find a tame element.
        T0 := [t : t in [1..3] | T[t] eq 0];
        for i in T0 do
          zetas[i] *:= Sqrt(1/mk(Norm(zetas[i])))@@mk;
        end for;
        for i := 2 to #T0 do
          zetas[T0[i]] +:= zetas[T0[1]];
        end for;
        T := [Valuation(Norm(z), pp) : z in zetas];
        mt, t := Max(T);
        if mt le 1 then
          J := ideal<O | [z : z in zetas | Valuation(Norm(z),pp) gt 0] cat Generators(pp)>;
        else
          J := ideal<O | [zetas[t]] cat Generators(pp)>;
        end if;      
      else
        J := ideal<O | [zetas[t]] cat Generators(pp)>;
      end if;
      if RightOrder(J) eq O then
        J +:= ideal<O | xi-1>;
      end if;
    end if;
    O := RightOrder(J);
  until Valuation(Discriminant(O), pp) le 1;

  rts := Roots(PolynomialRing(k) ! [mk(Norm(xi)), -mk(Trace(xi)), 1]);

  // Case that A is unramified at pp and O is not yet pp-maximal 
  if h eq 1 and Valuation(Discriminant(O), pp) eq 1 then
    if Valuation(Discriminant(O), pp) gt 0 then 
      // Case that k[xi] splits
      if #rts eq 2 then
        mkz := rts[1];
        z := mkz[1]@@mk;

        // Compute an element zeta in the pp-radical, i.e. 
        // Norm(zeta) = -zeta^2 is in pp  
        zetasgt0 := [zetas[t] : t in [1..#T] | T[t] gt 0];
        zetas0 := [zetas[t] : t in [1..#T] | T[t] eq 0];
        if zetasgt0 eq [] then
          zeta1 := zetas0[1];
          zeta2 := zetas0[#zetas0];
          zeta := (Sqrt(mk(Norm(zeta1)))@@mk)*zeta2 + 
                  (Sqrt(mk(Norm(zeta2)))@@mk)*zeta1;
        else
          zeta := zetasgt0[1];
        end if;

        J := ideal<O | [xi-z,zeta] cat Generators(pp)>;
        O := RightOrder(J);
        while Valuation(Discriminant(O), pp) gt 0 do
          ezeta := Valuation(Norm(zeta), pp);
          if ezeta eq 0 then
            if zeta in O then
              // Valuation (ezeta) is zero; need to add to it another
              // element of valuation zero to get something of larger
              // valuation.
              if #zetas0 gt 0 then
                zeta := (Sqrt(mk(Norm(zetas0[1])))@@mk)*zeta +
                        (Sqrt(mk(Norm(zeta)))@@mk)*zetas0[1];
              else
                zeta := zetasgt0[2];
              end if;
            else
              O := Adjoin(O, zeta);
            end if;
          elif ezeta gt 1 then
            zeta *:= piinvFp;
          end if;
          J := ideal<O | [xi-z,zeta] cat Generators(pp)>;
          O := RightOrder(J);
        end while;
      else
        // Case that k[xi] is unramified field extension
        zetas0 := [z : z in zetas | Valuation(Norm(z), pp) eq 0];
        zeta := zetas0[1];
        z := mk(Norm(zeta));
        z := Sqrt(z)@@mk;

        J := ideal<O | [zeta-z] cat Generators(pp)>;
        O := RightOrder(J);
      end if;
    end if;
  end if;

  if assigned Oold`TraceZeroInternalData then
    O`TraceZeroInternalData := Oold`TraceZeroInternalData;
  end if;

  O`FactoredDiscriminant := [qq : qq in FactoredDiscriminant(Oold) | qq[1] ne pp];
  O`Discriminant := 1*BaseRing(O);
  for qq in [qq : qq in O`FactoredDiscriminant] do
    O`Discriminant *:= qq[1]^qq[2];
  end for;

  if h eq -1 then
    O`FactoredDiscriminant cat:= [<pp, 1>];
    O`Discriminant *:= pp;
    return O, 1;
  else
    return O, 0;
  end if;
end function;

function QuaternionMaximalOrder(O)
//::AlgAssVOrd[RngOrd]) -> AlgAssVOrd
//{Computes a maximal order containing the order O (in a quaternion algebra).}

  if assigned O`IsMaximal and O`IsMaximal then
    return O;
  end if;

  A := Algebra(O);

  assert ISA(Type(A), AlgQuat);
  // absolute extensions only have been handled here
  assert CoefficientRing(CoefficientRing(O)) cmpeq Integers();

  if assigned A`MaximalOrder and &and[x in A`MaximalOrder : x in ZBasis(O)] then
    return A`MaximalOrder;
  end if;

  dOfact := FactoredDiscriminant(O);

  // Second step: for each odd prime, compute a p-maximal order
  vprintf K3Quat, 1 :
      "Computing p-maximal orders for %o primes...\n", #dOfact;
  dOfacteven := [];
  dOfactfinal := [];
  for idx->pp in dOfact do 
    // Skip the even primes; treat them below
      if Generator(pp[1] meet Integers()) eq 2 then
	  vprintf K3Quat, 1 :
	      "prime #%o is even, skipping for now...\n", idx;
	  Append(~dOfacteven, pp[1]);
	  continue pp;
      end if;
      vprintf K3Quat, 1 : "computing p-maximal order for prime #%o...", idx;
      O := pMaximalOrder(O, pp[1]);
      vprint K3Quat, 1 : "Done!\n";
  end for;

  vprintf K3Quat, 1 :
      "Computing p-maximal orders for %o even primes...\n", #dOfacteven;
  // Last major step: Cope with the even primes
  for idx->pp in dOfacteven do
      vprintf K3Quat, 1 : "computing p-maximal order for prime #%o...", idx;
      O := pEvenMaximalOrder(O, pp);
      vprintf K3Quat, 1 :  "Done!\n";
  end for;

  assert O`Discriminant eq Discriminant(O : Recompute := true);

  O`IsMaximal := true;
  return O;  
end function;

function MyOwnMaximalOrder(A)
    
  if assigned A`MaximalOrder then
    return A`MaximalOrder;
  end if;

  F := BaseField(A);

  // This might be an expensive step, but is necessary.
  // And it should need to be only called once per F.
  Z_F := MaximalOrder(F);

  // First compute a tame order, then make it maximal
  Otame := MyTameOrder(A);
  O := QuaternionMaximalOrder(Otame);
  A`MaximalOrder := O;
  return O;
end function;

intrinsic MyQuaternionAlgebra(I::RngOrdIdl,S::SeqEnum[PlcNumElt] :
			      Optimized := true) -> AlgQuat
{Returns the quaternion algebra which is ramified only at the primes dividing I and at the real places specified by S. By default, an optimized algebra (having small a,b) will be computed, which includes the computation of a maximal order; to avoid this, set Optimized to false.}
	  
  Z_F := Order(I);
  F := FieldOfFractions(Z_F);

  P := Factorization(I);
  assert IsEven(#P + #S);

  // For the first generator, take an element with valuation 1 at the primes
  // dividing I;
  if #P eq 0 then
    a := F!1;
  else
    a := WeakApproximation([p[1] : p in P], [1 : i in [1..#P]]);
  end if;
  // We take care of the real places here.  For each v in S, we need v(a) < 0,
  // and for each v not in S, we need v(a) > 0.
  // First, try to multiply a by a unit to achieve this;
  T := [];
  if #S ne 0 then 
    Foo := RealPlaces(NumberField(S[1]));
  else
    Foo := RealPlaces(F);
  end if;

  for v in Foo do
    if (v in S and Evaluate(a,v) gt 0) or (v notin S and Evaluate(a,v) lt 0) then
      Append(~T, -1);
    else
      Append(~T, 1);
    end if;
  end for;

  u := RealWeakApproximation(Foo, T : CoprimeTo := I);
  a *:= u;
  a := Z_F!a;

  a0 := a;

  if #P eq 0 and forall{pp : pp in Factorization(2*a*Z_F) | HilbertSymbol(F!-1,F!a,pp[1]) eq 1} and IsUnit(Z_F!u) then
    b := a;
    a := -1;
  else
  repeat
    // Now we need to find b with the following properties:
    // - For each prime p which divides I, we need (b/p) = -1;
    // - For each prime p which divides (a) but which does not divide I,
    //   we need (b/p) = 1; 
    // - For each even prime p which does not divide (a), we need (b/p) = 1;
    // - For each v in S, we need v(b) < 0;
    // - b generates a (principal) prime ideal.
    // Already in the case of the integers, we would need to find nonsquares, 
    // for which deterministic algorithms are dodgy, so we content ourselves
    // with a probablistic approach.
    Ps := [<p[1],1,false> : p in P | Valuation(Z_F!2, p[1]) eq 0] cat
          [<p[1],2*RamificationIndex(p[1])+1,false> : p in P | 
           Valuation(Z_F!2, p[1]) ne 0];
    if #Ps eq 0 then
      ps2 := Factorization(ideal<Z_F | a>);
    else
      ps2 := &*[p[1]^p[2] : p in Ps];
      ps2 := Factorization(ideal<Z_F | a>/(ideal<Z_F | a> + ps2));
    end if;
    Ps cat:= [<p[1],1,true> : p in ps2 | Valuation(Z_F!2, p[1]) eq 0] cat 
             [<p[1],2*RamificationIndex(p[1])+1,true> : p in ps2 | 
              Valuation(Z_F!2, p[1]) ne 0] cat
             [<p[1],2*RamificationIndex(p[1])+1,true> : p in Decomposition(Z_F,2) | 
              Valuation(ideal<Z_F | a>,p[1]) eq 0];
    m := &*[p[1]^p[2] : p in Ps];
    mgen := Generators(m)[#Generators(m)];
    mapPs := <>;
    for p in Ps do
      if p[2] gt 1 then
        Append(~mapPs, map<Z_F -> Parent(true) | x :-> HilbertSymbol(F!a,F!x,p[1]) eq 1>);
      else
        Append(~mapPs, map<Z_F -> Parent(true) | x :-> LegendreSymbol(x,p[1]) eq 1>);
      end if;
    end for;

    cnt := 0;
    Z_Fm, mZ_Fm := quo<Z_F | m>;
    Nm := Norm(m);
    n := Degree(F);
    bbnd := Max(20, Sqrt(Norm(m)));
    bbnd := Min(bbnd, 10^4); // SRD, Dec 2011

    cntbigloop := 0;
    repeat
      // Strategy is to pick a random b modulo m, multiply by an appropriate
      // unit to get the real valuations correct, then test prime-by-prime to
      // see if it fulfills the conditions above.
	cntbigloop +:= 1;
	vprintf K3Quat, 2 : "cntbigloop = %o\n", cntbigloop;
      cnt +:= 1;
      repeat
        b := Inverse(mZ_Fm)(mZ_Fm(Z_F ! [Random(Norm(m)) : i in [1..n]]));
      until ideal<Z_F | b> + m eq ideal<Z_F | 1>;

      Sminus := [v : v in Foo | (v in S and Evaluate(F!b,v) gt 0)];
      Splus := [v : v in S | v notin Sminus];

      ub := RealWeakApproximation(Sminus cat Splus, 
                                  [-1 : v in Sminus] cat [1 : v in Splus]);
      b *:= ub;
      i := 1;
      while i le #Ps and mapPs[i](b) eq Ps[i][3] do
        i +:= 1;
      end while;
      passed := i gt #Ps;
      if passed and not (IsPrime(b*Z_F) or IsUnit(b)) then
        // TO DO: choose m1 coprime to b, otherwise this will take a long time
        m1 := Generators(m)[1];
        ubm1 := RealWeakApproximation(Foo, RealSigns(b*m1)); 
        while cnt le bbnd and not (IsPrime(b*Z_F) or IsUnit(b)) do
          b +:= ubm1 * m1;
          cnt +:= 1;
        end while;
      end if;

      // Keep track if there are too many failures, increase the size
      // of the space we're looking in.
      if cnt gt bbnd then
        cnt := 0;
        m *:= 2;
        Z_Fm, mZ_Fm := quo<Z_F | m>;
        passed := false;
      end if;
    until passed or cntbigloop gt Maximum(2^(#Ps), 10); //10^(Maximum((#S) div 2, 1));

    vprintf K3Quat, 1 : "trying big loop again...\n";
    // Could choose new random a, but nevermind.
  until passed;
  end if;

  K := NumberField(F);
  vprintf K3Quat, 1 : "constructing Quaternion algebra...";
  A := QuaternionAlgebra<K | K!a, K!b>;
  vprintf K3Quat, 1 : "Done!\n";
  // We skip the check for efficiency reasons
  /* D, Doo := Discriminant(A);
  if (#P eq 0 and D ne ideal<Z_F | 1>) or (#P gt 0 and D ne &*[pp[1] : pp in P]) or
    #Doo ne #S then
    error "Algebra improperly computed, please report!", D, Doo;
  end if;
  */
 
  if not Optimized then
    return A;
  end if;
  vprintf K3Quat, 1 : "Constructing maximal order...";
  O := MyOwnMaximalOrder(A);
  vprintf K3Quat, 1 : "Done!\n";
  
//return OptimizedRepresentation(O);
  return AA where AA is OptimizedRepresentation(O); // don't return the map too --SRD
end intrinsic;
