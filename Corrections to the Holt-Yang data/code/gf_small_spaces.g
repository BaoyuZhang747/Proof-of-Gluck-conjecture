# Verification for the twenty vector spaces of dimension at most 12 that occur
# in Table 4.1 of Holt--Yang.  Every candidate-table row on each of these
# spaces is included, even when it has no Holt--Yang group file.  Large
# normalisers are treated by exact quotient enumerations or by the field and
# multiplicity reductions proved below.

RequireEqual := function(description, found, expected)
    if found <> expected then
        Error(description, "\nexpected: ", expected, "\nfound: ", found);
    fi;
end;;

RequireAndRead := function(path)
    if not IsReadableFile(path) then
        Error("The required input file is missing or unreadable: ", path);
    fi;
    Read(path);
end;;

if LoadPackage("irredsol") <> true then
    Error("The GAP package IrredSol is required.");
fi;

RequireAndRead("matrix_group_tests.g");

HoltYangDataDir := "holt_yang_data/";;

# The five defining conditions are the same conjunction as in
# SatisfiesHoltYangCriteria.  On the small spaces, however, most inverse images
# are reducible.  Testing irreducibility before sweeping the vectors avoids
# repeating a full vector-space calculation for groups that can be rejected
# immediately.  In a quotient calculation solvability is already known:
# both the prescribed normal subgroup and the quotient subgroup are solvable.
SatisfiesSmallSpaceCriteria := function(G, p, d, solvabilityKnown)
    if not solvabilityKnown and not IsSolvableGroup(G) then
        return false;
    fi;
    if not MTX.IsIrreducible(
               GModuleByMats(GeneratorsOfGroup(G), GF(p))) then
        return false;
    fi;
    if not HasNoRegularOrbit(G, p, d) then
        return false;
    fi;
    return IsQuasiprimitiveNonmetacyclicLinearGroup(G, p, d);
end;;

# An earlier approach enumerated all subgroups of the 22 row-112 overgroups.
# The calculation below instead uses 44 normaliser quotients, containing 4,272
# subgroup classes in total.  It is still important to make the normal-subgroup
# tests before examining all vectors.
# The same pc image and its normal subgroups are used for both
# quasiprimitivity and metacyclicity.
SatisfiesRow112Criteria := function(G, p, d)
    local module;
    module := GModuleByMats(GeneratorsOfGroup(G), GF(p));
    if not MTX.IsIrreducible(module) then
        return false;
    fi;
    if not IsQuasiprimitiveNonmetacyclicLinearGroup(G, p, d) then
        return false;
    fi;
    return HasNoRegularOrbit(G, p, d);
end;;

# 1. Construction of the prescribed extraspecial or symplectic-type subgroup
#    parameters.

# For a prime power e = r^n the prescribed subgroup is the central product of
# n extraspecial groups of order r^3, extended by a fourth root of unity when a
# symplectic-type subgroup "S" is required.  The generators are the standard
# Pauli matrices for odd r and tensor products of dihedral or quaternion
# generators for r=2.  When the row has field-reduction parameter a>1, the
# subgroup is first written over K=GF(p^a) in dimension e and is then restricted
# to GF(p) in dimension ea by replacing each entry with its multiplication
# matrix on K over GF(p).

PrimePowerData := function(e)
    local fs, r, n, x;
    fs := Set(FactorsInt(e));
    if Length(fs) <> 1 then
        Error("The parameter e = ", e, " is not a prime power.");
    fi;
    r := fs[1];
    n := 0; x := e;
    while x > 1 do x := x / r; n := n + 1; od;
    return rec(r := r, n := n);
end;;

ScalarMatrix := function(n, alpha, K)
    local m, i;
    m := NullMat(n, n, K);
    for i in [1 .. n] do m[i][i] := alpha; od;
    return m;
end;;

# The matrix acting as localMat on the chosen tensor slot and trivially on the
# others, on the standard basis of (K^2)^{tensor n} indexed by bit-tuples.
SlotMatrix := function(K, n, slot, localMat)
    local tuples, dim, mat, row, tup, colBit, val, out, pos;
    tuples := Tuples([0, 1], n);
    dim := Length(tuples);
    mat := NullMat(dim, dim, K);
    for row in [1 .. dim] do
        tup := tuples[row];
        for colBit in [0, 1] do
            val := localMat[tup[slot] + 1][colBit + 1];
            if val <> Zero(K) then
                out := ShallowCopy(tup);
                out[slot] := colBit;
                pos := Position(tuples, out);
                mat[row][pos] := val;
            fi;
        od;
    od;
    return mat;
end;;

# A quaternion (Q8) generating pair over K: A of order 4 and B with B^2 = -1.
QuaternionPair := function(K)
    local z, o, minusOne, elts, c, d, A, B;
    z := Zero(K); o := One(K); minusOne := -o;
    A := [[z, o], [minusOne, z]];
    elts := Elements(K);
    for c in elts do
        for d in elts do
            if c^2 + d^2 = minusOne then
                B := [[c, d], [d, -c]];
                return [A, B];
            fi;
        od;
    od;
    Error("There is no quaternion pair over the field of order ", Size(K), ".");
end;;

# A dihedral (D8) generating pair over K.
DihedralPair := function(K)
    local z, o, minusOne;
    z := Zero(K); o := One(K); minusOne := -o;
    return [[[o, z], [z, minusOne]], [[z, o], [o, z]]];
end;;

# The extraspecial 2-subgroup of plus type (all D8 slots) or minus type (one Q8
# slot); n tensor slots, dimension 2^n.
BinaryExtraspecialGenerators := function(K, n, kind)
    local gens, q8, d8, slot, pair;
    gens := [];
    q8 := QuaternionPair(K);
    d8 := DihedralPair(K);
    for slot in [1 .. n] do
        if kind = "E-" and slot = n then
            pair := q8;
        else
            pair := d8;
        fi;
        Add(gens, SlotMatrix(K, n, slot, pair[1]));
        Add(gens, SlotMatrix(K, n, slot, pair[2]));
    od;
    return gens;
end;;

# The symplectic-type subgroup S is the central product of the plus-type
# extraspecial 2-subgroup E with the cyclic scalar group of order four.
SymplecticTypeGenerators := function(K, n)
    local q, iota, gens, dim;
    q := Size(K);
    iota := Z(q) ^ ((q - 1) / 4);
    gens := BinaryExtraspecialGenerators(K, n, "E+");
    dim := 2 ^ n;
    Add(gens, ScalarMatrix(dim, iota, K));
    return gens;
end;;

# The extraspecial r-subgroup for odd r: n slots of Pauli shift/clock matrices,
# dimension r^n, with omega a primitive r-th root of unity in K.
PauliGenerators := function(K, r, n, omega)
    local tuples, dim, gens, slot, X, Z, row, tup, out, pos;
    tuples := Tuples([0 .. r - 1], n);
    dim := Length(tuples);
    gens := [];
    for slot in [1 .. n] do
        X := NullMat(dim, dim, K);
        Z := NullMat(dim, dim, K);
        for row in [1 .. dim] do
            tup := tuples[row];
            out := ShallowCopy(tup);
            out[slot] := (out[slot] + 1) mod r;
            pos := Position(tuples, out);
            X[row][pos] := One(K);
            Z[row][row] := omega ^ tup[slot];
        od;
        Add(gens, X);
        Add(gens, Z);
    od;
    return gens;
end;;

# Generators of the prescribed subgroup, written over K = GF(q), in dimension e.
CoreGeneratorsOverField := function(q, pp, kind)
    local K, omega;
    K := GF(q);
    if pp.r = 2 then
        if kind = "S" then
            return SymplecticTypeGenerators(K, pp.n);
        fi;
        return BinaryExtraspecialGenerators(K, pp.n, kind);
    fi;
    omega := Z(q) ^ ((q - 1) / pp.r);
    return PauliGenerators(K, pp.r, pp.n, omega);
end;;

# The matrix of multiplication by alpha on K, in the basis "basis", over F.
MultiplicationMatrix := function(K, F, basis, alpha)
    local a, out, i, j, coeffs;
    a := Length(basis);
    out := NullMat(a, a, F);
    for i in [1 .. a] do
        coeffs := Coefficients(basis, basis[i] * alpha);
        for j in [1 .. a] do out[i][j] := coeffs[j]; od;
    od;
    return out;
end;;

# Blow a matrix over K up to a matrix over the prime field F by the regular
# representation of K over F (each entry becomes an a x a block).
BlowUpMatrix := function(K, F, mat)
    local basis, a, m, out, i, j, block, bi, bj;
    basis := Basis(K);
    a := Length(basis);
    m := Length(mat);
    out := NullMat(m * a, m * a, F);
    for i in [1 .. m] do
        for j in [1 .. m] do
            block := MultiplicationMatrix(K, F, basis, mat[i][j]);
            for bi in [1 .. a] do
                for bj in [1 .. a] do
                    out[(i - 1) * a + bi][(j - 1) * a + bj] := block[bi][bj];
                od;
            od;
        od;
    od;
    return out;
end;;

# Recover the subgroup used in a restriction-of-scalars calculation from its
# local linear normaliser.  For odd r the subgroup is Omega_1(O_r(N)); for a
# symplectic-type 2-group it is generated by the elements of O_2(N) whose
# fourth power is trivial.  In the remaining calculation below the prescribed
# group is the minus-type extraspecial group and is O_2(N).  The plus type in
# row 72 is covered by the separate conjugacy with row 111 and is not passed to
# this test: its local normaliser has a larger 2-core.
CertifyCharacteristicLocalSubgroup := function(core, prescribed, normaliser)
    local r, radical, intrinsic;
    r := PrimePowerData(core.e).r;
    radical := PCore(normaliser, r);
    if r <> 2 then
        intrinsic := Group(Filtered(Elements(radical),
            x -> x ^ r = One(radical)));
    elif core.kind = "S" then
        intrinsic := Group(Filtered(Elements(radical),
            x -> x ^ 4 = One(radical)));
    else
        intrinsic := radical;
    fi;
    RequireEqual(Concatenation("intrinsic prescribed subgroup in the local ",
                            "normaliser for row ", core.row),
              intrinsic, prescribed);
end;;

# Build the prescribed subgroup E<=GL(d,p) and its full normaliser N in
# GL(d,p), using the row record with fields p, e, a, d and kind.  For a=1 the
# generators already lie over GF(p); for a>1 they are obtained by restriction
# of scalars from GF(p^a).
CoreAndNormaliser := function(core)
    local p, e, a, d, kind, pp, F, K, q, E, localMatrices, localCore,
          localNormaliser;
    p := core.p; e := core.e; a := core.a; d := core.d; kind := core.kind;
    pp := PrimePowerData(e);
    F := GF(p);
    if a = 1 then
        E := Group(List(CoreGeneratorsOverField(p, pp, kind), m -> One(F) * m));
    else
        q := p ^ a;
        K := GF(q);
        localMatrices := CoreGeneratorsOverField(q, pp, kind);
        localCore := Group(localMatrices);
        localNormaliser := Normalizer(GL(e, q), localCore);
        CertifyCharacteristicLocalSubgroup(
            core, localCore, localNormaliser);
        E := Group(List(localMatrices,
                        g -> BlowUpMatrix(K, F, g)));
    fi;
    return rec(E := E, N := Normalizer(GL(d, p), E));
end;;

# The tensor product is ordered with the multiplicity coordinate varying
# fastest.  The next two routines embed the local and multiplicity actions in
# that basis.
InflateLocalMatrix := function(A, b, F)
    local e, out, i, j, r;
    e := Length(A);
    out := NullMat(e * b, e * b, F);
    for i in [1 .. e] do
        for j in [1 .. e] do
            for r in [1 .. b] do
                out[(i - 1) * b + r][(j - 1) * b + r] := A[i][j];
            od;
        od;
    od;
    return out;
end;;

InflateMultiplicityMatrix := function(B, e, F)
    local b, out, i, r, c;
    b := Length(B);
    out := NullMat(e * b, e * b, F);
    for i in [1 .. e] do
        for r in [1 .. b] do
            for c in [1 .. b] do
                out[(i - 1) * b + r][(i - 1) * b + c] := B[r][c];
            od;
        od;
    od;
    return out;
end;;

FrobeniusMatrix := function(K, F)
    local basis, a, out, i, j, coeffs;
    basis := Basis(K);
    a := Length(basis);
    out := NullMat(a, a, F);
    for i in [1 .. a] do
        coeffs := Coefficients(basis, basis[i] ^ Size(F));
        for j in [1 .. a] do out[i][j] := coeffs[j]; od;
    od;
    return out;
end;;

RepeatDiagonalBlock := function(block, copies, F)
    local a, out, k, i, j;
    a := Length(block);
    out := NullMat(a * copies, a * copies, F);
    for k in [1 .. copies] do
        for i in [1 .. a] do
            for j in [1 .. a] do
                out[(k - 1) * a + i][(k - 1) * a + j] := block[i][j];
            od;
        od;
    od;
    return out;
end;;

ParametricCore := function(core)
    local pp, F, K, mats, localMats;
    pp := PrimePowerData(core.e);
    F := GF(core.p);
    if core.a = 1 then
        localMats := List(CoreGeneratorsOverField(core.p, pp, core.kind),
                          A -> One(F) * A);
        if core.b = 1 then return Group(localMats); fi;
        return Group(List(localMats,
                          A -> InflateLocalMatrix(A, core.b, F)));
    fi;
    K := GF(core.p ^ core.a);
    localMats := CoreGeneratorsOverField(Size(K), pp, core.kind);
    if core.b > 1 then
        localMats := List(localMats,
                          A -> InflateLocalMatrix(A, core.b, K));
    fi;
    mats := List(localMats, A -> BlowUpMatrix(K, F, A));
    return Group(mats);
end;;

MultiplicityCoreData := function(core)
    local F, pp, localCore, localN, inflatedCore, localAction, multiplicity, gens,
          multiplicityGens, A, B;
    F := GF(core.p);
    pp := PrimePowerData(core.e);
    localCore := Group(List(CoreGeneratorsOverField(core.p, pp, core.kind),
                            A -> One(F) * A));
    localN := Normalizer(GL(core.e, core.p), localCore);
    inflatedCore := Group(List(GeneratorsOfGroup(localCore),
                               A -> InflateLocalMatrix(A, core.b, F)));
    gens := List(GeneratorsOfGroup(localN),
                 A -> InflateLocalMatrix(A, core.b, F));
    localAction := Group(gens);
    multiplicityGens := List(GeneratorsOfGroup(GL(core.b, core.p)),
                             B -> InflateMultiplicityMatrix(B, core.e, F));
    multiplicity := Group(multiplicityGens);
    Append(gens, multiplicityGens);
    return rec(E := inflatedCore, N := Group(gens), localCore := localCore,
               localNormaliser := localN, localAction := localAction,
               multiplicity := multiplicity);
end;;

SemilinearCoreData := function(core)
    local pp, F, K, basis, localCore, localN, inflatedCore, linearNormaliser, gens, A,
          frob, fieldGenerator;
    pp := PrimePowerData(core.e);
    F := GF(core.p);
    K := GF(core.p ^ core.a);
    localCore := Group(CoreGeneratorsOverField(Size(K), pp, core.kind));
    localN := Normalizer(GL(core.e, Size(K)), localCore);
    inflatedCore := Group(List(GeneratorsOfGroup(localCore),
                               A -> BlowUpMatrix(K, F, A)));
    gens := List(GeneratorsOfGroup(localN),
                 A -> BlowUpMatrix(K, F, A));
    linearNormaliser := Group(gens);
    frob := RepeatDiagonalBlock(FrobeniusMatrix(K, F), core.e, F);
    basis := Basis(K);
    fieldGenerator := RepeatDiagonalBlock(
        MultiplicationMatrix(K, F, basis, Z(Size(K))), core.e, F);
    Add(gens, frob);
    return rec(E := inflatedCore, linearNormaliser := linearNormaliser,
               N := Group(gens),
               localCore := localCore, localNormaliser := localN,
               fieldGenerator := fieldGenerator);
end;;

# For a row with a>1, the structural reduction places the group in
# GammaL(e,p^a).  Its linear part normalises the prescribed subgroup in
# GL(e,p^a), and its image in Gal(GF(p^a)/GF(p)) has order dividing a.  Thus the
# group constructed above, from the local normaliser and Frobenius, is the
# required row-specific overgroup.  Notice that the prescribed subgroup itself
# need not be irreducible after restriction of scalars: when its matrices are
# already defined over GF(p), it acts as the direct sum of a copies of its local
# module.  The linear overgroup contains all GF(p^a)-scalars and has
# endomorphism field GF(p^a).
CertifySemilinearNormaliser := function(core, data, p, d)
    local module, endomorphisms, fieldPowers, fieldScalars;
    CertifyCharacteristicLocalSubgroup(
        core, data.localCore, data.localNormaliser);
    RequireEqual(Concatenation("local prescribed subgroup normal in its computed normaliser ",
                            "for row ", core.row),
              IsNormal(data.localNormaliser, data.localCore), true);
    RequireEqual(Concatenation("faithful field reduction for row ", core.row),
              Size(data.linearNormaliser), Size(data.localNormaliser));
    RequireEqual(Concatenation("prescribed subgroup normal in the semilinear normaliser for row ",
                            core.row), IsNormal(data.N, data.E), true);
    RequireEqual(Concatenation("field-reduced local normaliser normal in the ",
                            "semilinear overgroup for row ", core.row),
              IsNormal(data.N, data.linearNormaliser), true);
    RequireEqual(Concatenation("semilinear cosets for row ", core.row),
              Size(data.N), core.a * Size(data.linearNormaliser));
    module := GModuleByMats(GeneratorsOfGroup(data.linearNormaliser), GF(p));
    RequireEqual(Concatenation("irreducible field-reduced local normaliser for row ",
                            core.row), MTX.IsIrreducible(module), true);
    endomorphisms := MTX.BasisModuleEndomorphisms(module);
    RequireEqual(Concatenation("endomorphism-field degree of the field-reduced ",
                            "local normaliser for row ", core.row),
              Length(endomorphisms), core.a);
    RequireEqual(Concatenation("order of the embedded field generator for row ",
                            core.row), Order(data.fieldGenerator),
              p ^ core.a - 1);
    RequireEqual(Concatenation("embedded field centralises the field-reduced ",
                            "local normaliser for row ", core.row),
      ForAll(GeneratorsOfGroup(data.linearNormaliser),
             g -> g * data.fieldGenerator = data.fieldGenerator * g), true);
    fieldPowers := List([0 .. core.a - 1],
                        i -> Flat(data.fieldGenerator ^ i));
    RequireEqual(Concatenation("embedded field-algebra dimension for row ",
                            core.row), RankMat(fieldPowers), core.a);
    fieldScalars := Group(data.fieldGenerator);
    RequireEqual(Concatenation("semilinear group normalises the embedded field for row ",
                            core.row), IsNormal(data.N, fieldScalars), true);
end;;

# For a multiplicity row the local prescribed subgroup is absolutely
# irreducible and its b
# identical copies have endomorphism algebra Mat_b(GF(p)).  Hence a normaliser
# consists of a local normaliser and a multiplicity change of basis, with the
# scalar intersection of order p-1.  The asserted order attains this upper
# bound and proves that the constructed group is the full normaliser of the
# prescribed subgroup.
CertifyMultiplicityNormaliser := function(core, data, p, d)
    local localModule, coreModule, endomorphisms, expectedOrder,
          multiplicityAlgebra;
    localModule := GModuleByMats(GeneratorsOfGroup(data.localCore), GF(p));
    RequireEqual(Concatenation("absolutely irreducible local core for row ",
                            core.row),
              MTX.IsAbsolutelyIrreducible(localModule), true);
    RequireEqual(Concatenation("local core normal in its computed normaliser ",
                            "for row ", core.row),
              IsNormal(data.localNormaliser, data.localCore), true);
    RequireEqual(Concatenation("core normal in the multiplicity normaliser for ",
                            "row ", core.row), IsNormal(data.N, data.E), true);
    RequireEqual(Concatenation("faithful local action for row ", core.row),
              Size(data.localAction), Size(data.localNormaliser));
    RequireEqual(Concatenation("multiplicity GL contained in the normaliser for ",
                            "row ", core.row),
              IsSubgroup(data.N, data.multiplicity), true);
    RequireEqual(Concatenation("multiplicity GL centralises the core for row ",
                            core.row),
      ForAll(GeneratorsOfGroup(data.multiplicity), g ->
        ForAll(GeneratorsOfGroup(data.E), s -> g * s = s * g)), true);
    RequireEqual(Concatenation("commuting tensor factors for row ", core.row),
      ForAll(GeneratorsOfGroup(data.multiplicity), g ->
        ForAll(GeneratorsOfGroup(data.localAction), h -> g * h = h * g)),
      true);
    RequireEqual(Concatenation("scalar intersection in the tensor factors for ",
                            "row ", core.row),
              Size(Intersection(data.localAction, data.multiplicity)), p - 1);
    RequireEqual(Concatenation("generation by the two tensor factors for row ",
                            core.row),
              ClosureGroup(data.localAction, data.multiplicity), data.N);
    coreModule := GModuleByMats(GeneratorsOfGroup(data.E), GF(p));
    endomorphisms := MTX.BasisModuleEndomorphisms(coreModule);
    RequireEqual(Concatenation("multiplicity endomorphism-algebra dimension for ",
                            "row ", core.row),
              Length(endomorphisms), core.b ^ 2);
    multiplicityAlgebra := AlgebraWithOne(
        GF(p), GeneratorsOfGroup(data.multiplicity));
    RequireEqual(Concatenation("explicit multiplicity-algebra dimension for ",
                            "row ", core.row),
              Dimension(multiplicityAlgebra), core.b ^ 2);
    expectedOrder := Size(data.localNormaliser) * Size(GL(core.b, p))
                     / (p - 1);
    RequireEqual(Concatenation("tensor-product normaliser order for row ",
                            core.row), Size(data.N), expectedOrder);
end;;

CoreDataForMethod := function(core)
    if PositionSublist(core.method, "multiplicity") = 1 then
        return MultiplicityCoreData(core);
    fi;
    if PositionSublist(core.method, "semilinear") = 1 then
        return SemilinearCoreData(core);
    fi;
    return CoreAndNormaliser(core);
end;;

# For p=3,11,19 the normaliser of a plus-type extraspecial subgroup of
# GL(2,p) is conjugate to a subgroup of the normaliser of a minus-type one.
# The matrices below prove this directly.  The intermediate quaternion group
# Q0 is used so that the calculation does not depend on which quaternion pair
# is returned by QuaternionPair.
LocalPlusNormaliserEmbedding := function(p, Eminus, Nminus)
    local F, zero, one, A, B, g, Q0, Eplus, N0, Nplus, y, u;
    F := GF(p);
    zero := Zero(F);
    one := One(F);
    A := [[zero, one], [-one, zero]];
    if p = 3 then
        B := one * [[1, 1], [1, -1]];
        g := one * [[0, 1], [1, 0]];
    elif p = 11 then
        B := one * [[1, 3], [3, -1]];
        g := one * [[0, 1], [3, -1]];
    elif p = 19 then
        B := one * [[1, 6], [6, -1]];
        g := one * [[0, 1], [6, -1]];
    else
        Error("No plus-normaliser inclusion is prescribed for p = ", p, ".");
    fi;
    Q0 := Group([A, B]);
    Eplus := Group(DihedralPair(F));
    N0 := Normalizer(GL(2, p), Q0);
    Nplus := Normalizer(GL(2, p), Eplus);
    RequireEqual(Concatenation("order of the standard minus-type subgroup in GL(2,",
                            String(p), ")"), Size(Q0), 8);
    RequireEqual(Concatenation("involutions in the standard minus-type subgroup in GL(2,",
                            String(p), ")"),
                 Number(Elements(Q0), x -> Order(x) = 2), 1);
    RequireEqual(Concatenation("order of the standard plus-type subgroup in GL(2,",
                            String(p), ")"), Size(Eplus), 8);
    RequireEqual(Concatenation("involutions in the standard plus-type subgroup in GL(2,",
                            String(p), ")"),
                 Number(Elements(Eplus), x -> Order(x) = 2), 5);
    RequireEqual(Concatenation("order of the plus-type normaliser in GL(2,",
                            String(p), ")"), Size(Nplus), 8 * (p - 1));
    RequireEqual(Concatenation("order of the minus-type normaliser in GL(2,",
                            String(p), ")"), Size(N0), 24 * (p - 1));
    RequireEqual(Concatenation("the displayed matrix embeds the plus-type normaliser in ",
                            "the standard minus-type normaliser for p = ", String(p)),
                 IsSubgroup(N0, Nplus ^ g), true);
    y := RepresentativeAction(GL(2, p), Q0, Eminus);
    RequireEqual(Concatenation("conjugacy of the two minus-type subgroups for p = ",
                            String(p)), y <> fail, true);
    RequireEqual(Concatenation("the displayed conjugator carries the standard minus-type ",
                            "subgroup to the prescribed one for p = ", String(p)),
                 Q0 ^ y, Eminus);
    u := g * y;
    RequireEqual(Concatenation("the plus-type normaliser lies in the prescribed minus-type ",
                            "normaliser for p = ", String(p)),
                 IsSubgroup(Nminus, Nplus ^ u), true);
    return rec(core := Eplus, normaliser := Nplus, conjugator := u);
end;;

# 2. The twenty spaces, their prescribed subgroups, and their Holt--Yang files.

# For each space:
#   cores            -- one record for every row-and-type calculation on the space.
#   holtYangFiles     -- the Holt--Yang Line*.g files used for comparison.
#   listed           -- the number of groups in those files.
#   distinct         -- the number of GL(d,p)-conjugacy classes they represent.

Spaces := [
  rec(key:="3^2", p:=3, d:=2, holtYangFiles:=["Line62gps"], listed:=2, distinct:=2,
      cores:=[
        rec(row:="62E-",p:=3,e:=2,a:=1,b:=1,d:=2,kind:="E-",method:="direct",nOrder:=48,classCount:=16,acceptedCount:=2),
        rec(row:="62E+",p:=3,e:=2,a:=1,b:=1,d:=2,kind:="E+",method:="contained",coveredByIndex:=1,nOrder:=16,classCount:=0,acceptedCount:=0)]),
  rec(key:="5^2", p:=5, d:=2, holtYangFiles:=["Line63gps"], listed:=2, distinct:=2,
      cores:=[rec(row:="63",p:=5,e:=2,a:=1,b:=1,d:=2,kind:="S",method:="direct",nOrder:=96,classCount:=24,acceptedCount:=2)]),
  rec(key:="7^2", p:=7, d:=2, holtYangFiles:=["Line64gps"], listed:=2, distinct:=2,
      cores:=[
        rec(row:="64E-",p:=7,e:=2,a:=1,b:=1,d:=2,kind:="E-",method:="direct",nOrder:=144,classCount:=29,acceptedCount:=2),
        rec(row:="64E+",p:=7,e:=2,a:=1,b:=1,d:=2,kind:="E+",method:="quotient",nOrder:=48,classCount:=4,acceptedCount:=0)]),
  rec(key:="11^2", p:=11, d:=2, holtYangFiles:=["Line66gps"], listed:=2, distinct:=2,
      cores:=[
        rec(row:="66E-",p:=11,e:=2,a:=1,b:=1,d:=2,kind:="E-",method:="direct",nOrder:=240,classCount:=32,acceptedCount:=2),
        rec(row:="66E+",p:=11,e:=2,a:=1,b:=1,d:=2,kind:="E+",method:="contained",coveredByIndex:=1,nOrder:=80,classCount:=0,acceptedCount:=0)]),
  rec(key:="13^2", p:=13, d:=2, holtYangFiles:=["Line67gps"], listed:=2, distinct:=2,
      cores:=[rec(row:="67",p:=13,e:=2,a:=1,b:=1,d:=2,kind:="S",method:="direct",nOrder:=288,classCount:=53,acceptedCount:=2)]),
  rec(key:="17^2", p:=17, d:=2, holtYangFiles:=["Line68gps"], listed:=3, distinct:=3,
      cores:=[rec(row:="68",p:=17,e:=2,a:=1,b:=1,d:=2,kind:="S",method:="direct",nOrder:=384,classCount:=87,acceptedCount:=3)]),
  rec(key:="19^2", p:=19, d:=2, holtYangFiles:=["Line69gps"], listed:=2, distinct:=2,
      cores:=[
        rec(row:="69E-",p:=19,e:=2,a:=1,b:=1,d:=2,kind:="E-",method:="direct",nOrder:=432,classCount:=54,acceptedCount:=2),
        rec(row:="69E+",p:=19,e:=2,a:=1,b:=1,d:=2,kind:="E+",method:="contained",coveredByIndex:=1,nOrder:=144,classCount:=0,acceptedCount:=0)]),

  rec(key:="7^3", p:=7, d:=3, holtYangFiles:=["Line49gps"], listed:=4, distinct:=4,
      cores:=[rec(row:="49",p:=7,e:=3,a:=1,b:=1,d:=3,kind:="E3",method:="direct",nOrder:=1296,classCount:=102,acceptedCount:=4)]),
  rec(key:="13^3", p:=13, d:=3, holtYangFiles:=["Line50gps"], listed:=2, distinct:=2,
      cores:=[rec(row:="50",p:=13,e:=3,a:=1,b:=1,d:=3,kind:="E3",method:="direct",nOrder:=2592,classCount:=166,acceptedCount:=2)]),
  rec(key:="19^3", p:=19, d:=3, holtYangFiles:=["Line52gps"], listed:=1, distinct:=1,
      cores:=[rec(row:="52",p:=19,e:=3,a:=1,b:=1,d:=3,kind:="E3",method:="direct",nOrder:=3888,classCount:=216,acceptedCount:=1)]),

  rec(key:="3^4", p:=3, d:=4, holtYangFiles:=["Line19gpsp","Line19gpsm","Line65gps"], listed:=36, distinct:=24,
      cores:=[
        rec(row:="19E+",p:=3,e:=4,a:=1,b:=1,d:=4,kind:="E+",method:="direct",nOrder:=2304,classCount:=310,acceptedCount:=21),
        rec(row:="19E-",p:=3,e:=4,a:=1,b:=1,d:=4,kind:="E-",method:="direct",nOrder:=3840,classCount:=221,acceptedCount:=19),
        rec(row:="65",p:=3,e:=2,a:=2,b:=1,d:=4,kind:="S",method:="direct",nOrder:=384,classCount:=254,acceptedCount:=16),
        rec(row:="104E-",p:=3,e:=2,a:=1,b:=2,d:=4,kind:="E-",method:="multiplicity-direct",nOrder:=1152,classCount:=317,acceptedCount:=31),
        rec(row:="104E+",p:=3,e:=2,a:=1,b:=2,d:=4,kind:="E+",method:="multiplicity-contained",coveredByIndex:=4,nOrder:=384,classCount:=0,acceptedCount:=0)]),
  rec(key:="5^4", p:=5, d:=4, holtYangFiles:=["Line20gps","Line71gps"], listed:=38, distinct:=38,
      cores:=[
        rec(row:="20",p:=5,e:=4,a:=1,b:=1,d:=4,kind:="S",method:="direct",nOrder:=46080,classCount:=1313,acceptedCount:=24),
        rec(row:="71",p:=5,e:=2,a:=2,b:=1,d:=4,kind:="S",method:="direct",nOrder:=11520,classCount:=983,acceptedCount:=26),
        rec(row:="105",p:=5,e:=2,a:=1,b:=2,d:=4,kind:="S",method:="multiplicity-direct",nOrder:=11520,classCount:=983,acceptedCount:=26)]),
  rec(key:="7^4", p:=7, d:=4, holtYangFiles:=["Line21gpsp","Line74gps"], listed:=23, distinct:=22,
      cores:=[
        rec(row:="21E+",p:=7,e:=4,a:=1,b:=1,d:=4,kind:="E+",method:="direct",nOrder:=6912,classCount:=647,acceptedCount:=17),
        rec(row:="21E-",p:=7,e:=4,a:=1,b:=1,d:=4,kind:="E-",method:="direct",nOrder:=11520,classCount:=447,acceptedCount:=0),
        rec(row:="74",p:=7,e:=2,a:=2,b:=1,d:=4,kind:="S",method:="direct",nOrder:=2304,classCount:=732,acceptedCount:=7),
        rec(row:="106E-",p:=7,e:=2,a:=1,b:=2,d:=4,kind:="E-",method:="multiplicity-direct",nOrder:=48384,classCount:=1487,acceptedCount:=17),
        rec(row:="106E+",p:=7,e:=2,a:=1,b:=2,d:=4,kind:="E+",method:="multiplicity-quotient",nOrder:=16128,classCount:=147,acceptedCount:=0)]),
  rec(key:="11^4", p:=11, d:=4, holtYangFiles:=["Line23gpsp"], listed:=4, distinct:=4,
      cores:=[
        rec(row:="23E+",p:=11,e:=4,a:=1,b:=1,d:=4,kind:="E+",method:="direct",nOrder:=11520,classCount:=620,acceptedCount:=4),
        rec(row:="23E-",p:=11,e:=4,a:=1,b:=1,d:=4,kind:="E-",method:="direct",nOrder:=19200,classCount:=445,acceptedCount:=0),
        rec(row:="76",p:=11,e:=2,a:=2,b:=1,d:=4,kind:="S",method:="semilinear-direct",nOrder:=5760,classCount:=1052,acceptedCount:=0),
        rec(row:="107E-",p:=11,e:=2,a:=1,b:=2,d:=4,kind:="E-",method:="multiplicity-direct",nOrder:=316800,classCount:=1964,acceptedCount:=0),
        rec(row:="107E+",p:=11,e:=2,a:=1,b:=2,d:=4,kind:="E+",method:="multiplicity-contained",coveredByIndex:=4,nOrder:=105600,classCount:=0,acceptedCount:=0)]),
  rec(key:="13^4", p:=13, d:=4, holtYangFiles:=["Line24gps"], listed:=5, distinct:=5,
      cores:=[
        rec(row:="24",p:=13,e:=4,a:=1,b:=1,d:=4,kind:="S",method:="quotient",nOrder:=138240,classCount:=201,acceptedCount:=5),
        rec(row:="78",p:=13,e:=2,a:=2,b:=1,d:=4,kind:="S",method:="semilinear-quotient",nOrder:=8064,classCount:=340,acceptedCount:=0),
        rec(row:="108",p:=13,e:=2,a:=1,b:=2,d:=4,kind:="S",method:="multiplicity-quotient",nOrder:=628992,classCount:=1225,acceptedCount:=0)]),
  rec(key:="17^4", p:=17, d:=4, holtYangFiles:=["Line25gps"], listed:=4, distinct:=4,
      cores:=[
        rec(row:="25",p:=17,e:=4,a:=1,b:=1,d:=4,kind:="S",method:="quotient",nOrder:=184320,classCount:=338,acceptedCount:=4),
        rec(row:="80",p:=17,e:=2,a:=2,b:=1,d:=4,kind:="S",method:="semilinear-quotient",nOrder:=13824,classCount:=469,acceptedCount:=0),
        rec(row:="109",p:=17,e:=2,a:=1,b:=2,d:=4,kind:="S",method:="multiplicity-quotient",nOrder:=1880064,classCount:=1947,acceptedCount:=0)]),

  rec(key:="2^6", p:=2, d:=6, holtYangFiles:=["Line48gps"], listed:=7, distinct:=7,
      cores:=[rec(row:="48",p:=2,e:=3,a:=2,b:=1,d:=6,kind:="E3",method:="direct",nOrder:=1296,classCount:=96,acceptedCount:=7)]),
  rec(key:="3^6", p:=3, d:=6, holtYangFiles:=["Line72gps"], listed:=2, distinct:=2,
      cores:=[
        rec(row:="72E-",p:=3,e:=2,a:=3,b:=1,d:=6,kind:="E-",method:="direct",nOrder:=269568,classCount:=2197,acceptedCount:=2),
        rec(row:="111E-",p:=3,e:=2,a:=1,b:=3,d:=6,kind:="E-",method:="duplicate",duplicateIndex:=1,nOrder:=269568,classCount:=0,acceptedCount:=0),
        rec(row:="111E+",p:=3,e:=2,a:=1,b:=3,d:=6,kind:="E+",method:="multiplicity-contained",coveredByIndex:=2,nOrder:=89856,classCount:=0,acceptedCount:=0),
        rec(row:="72E+",p:=3,e:=2,a:=3,b:=1,d:=6,kind:="E+",method:="duplicate",duplicateIndex:=3,nOrder:=89856,classCount:=0,acceptedCount:=0)]),
  rec(key:="5^6", p:=5, d:=6, holtYangFiles:=["Line53gps"], listed:=3, distinct:=3,
      cores:=[
        rec(row:="53",p:=5,e:=3,a:=2,b:=1,d:=6,kind:="E3",method:="direct",nOrder:=10368,classCount:=657,acceptedCount:=3),
        rec(row:="77",p:=5,e:=2,a:=3,b:=1,d:=6,kind:="S",method:="semilinear-direct",nOrder:=8928,classCount:=106,acceptedCount:=0),
        rec(row:="112",p:=5,e:=2,a:=1,b:=3,d:=6,kind:="S",method:="row112",nOrder:=35712000,classCount:=4272,acceptedCount:=0)]),
  rec(key:="2^12", p:=2, d:=12, holtYangFiles:=["Line51gps"], listed:=8, distinct:=8,
      cores:=[
        rec(row:="51",p:=2,e:=3,a:=4,b:=1,d:=12,kind:="E3",method:="direct",nOrder:=77760,classCount:=1535,acceptedCount:=8),
        rec(row:="115",p:=2,e:=3,a:=2,b:=2,d:=12,kind:="E3",method:="duplicate",duplicateIndex:=1,nOrder:=77760,classCount:=0,acceptedCount:=0)])
];;

# The records above transcribe every candidate-table row on these twenty
# spaces, with separate records when both extraspecial types are calculated.
# This independent list fixes each row-and-type calculation and its ambient
# enumeration.
ExpectedRowsBySpace := [
  ["3^2",   [["62E-", "direct"],
              ["62E+", "contained"]]],
  ["5^2",   [["63",   "direct"]]],
  ["7^2",   [["64E-", "direct"],
              ["64E+", "quotient"]]],
  ["11^2",  [["66E-", "direct"],
              ["66E+", "contained"]]],
  ["13^2",  [["67",   "direct"]]],
  ["17^2",  [["68",   "direct"]]],
  ["19^2",  [["69E-", "direct"],
              ["69E+", "contained"]]],
  ["7^3",   [["49",   "direct"]]],
  ["13^3",  [["50",   "direct"]]],
  ["19^3",  [["52",   "direct"]]],
  ["3^4",   [["19E+", "direct"],
              ["19E-", "direct"],
              ["65",   "direct"],
              ["104E-", "multiplicity-direct"],
              ["104E+", "multiplicity-contained"]]],
  ["5^4",   [["20",   "direct"],
              ["71",   "direct"],
              ["105",  "multiplicity-direct"]]],
  ["7^4",   [["21E+", "direct"],
              ["21E-", "direct"],
              ["74",   "direct"],
              ["106E-", "multiplicity-direct"],
              ["106E+", "multiplicity-quotient"]]],
  ["11^4",  [["23E+", "direct"],
              ["23E-", "direct"],
              ["76",   "semilinear-direct"],
              ["107E-", "multiplicity-direct"],
              ["107E+", "multiplicity-contained"]]],
  ["13^4",  [["24",   "quotient"],
              ["78",   "semilinear-quotient"],
              ["108",  "multiplicity-quotient"]]],
  ["17^4",  [["25",   "quotient"],
              ["80",   "semilinear-quotient"],
              ["109",  "multiplicity-quotient"]]],
  ["2^6",   [["48",   "direct"]]],
  ["3^6",   [["72E-",  "direct"],
              ["111E-", "duplicate"],
              ["111E+", "multiplicity-contained"],
              ["72E+",  "duplicate"]]],
  ["5^6",   [["53",   "direct"],
              ["77",   "semilinear-direct"],
              ["112",  "row112"]]],
  ["2^12",  [["51",   "direct"],
              ["115",  "duplicate"]]]
];;

RowsBySpace := List(Spaces,
    space -> [space.key,
              List(space.cores, core -> [core.row, core.method])]);;
RequireEqual("the complete row-and-type list", RowsBySpace,
          ExpectedRowsBySpace);
RequireEqual("the number of row-and-type calculations on the twenty spaces",
          Sum(Spaces, space -> Length(space.cores)), 48);

# 3. Read the Holt--Yang group files.

for space in Spaces do
    for name in space.holtYangFiles do
        RequireAndRead(Concatenation(HoltYangDataDir, name, ".g"));
        if not IsBoundGlobal(name) then
            Error("The file ", name, ".g did not define the list ", name,
                  ".");
        fi;
    od;
od;

# 4. Per-space enumeration and comparison.

# Is G GL(d,p)-conjugate to some group in the list "reps"?  The
# characteristic-polynomial invariant avoids impossible exact tests.
ConjugateToSome := function(G, invariant, reps, repInvariants, p)
    local j;
    for j in [1 .. Length(reps)] do
        if repInvariants[j] = invariant
           and AreConjugateInGL(G, reps[j], p) then
            return true;
        fi;
    od;
    return false;
end;;

# Exact pairs of conjugate groups in two ordered lists.  The invariant is used
# only to avoid impossible module-isomorphism tests.
ExactGLConjugacyPairs := function(left, leftInvariants,
                                   right, rightInvariants, p)
    local pairs, i, j;
    pairs := [];
    for i in [1 .. Length(left)] do
        for j in [1 .. Length(right)] do
            if leftInvariants[i] = rightInvariants[j]
               and AreConjugateInGL(left[i], right[j], p) then
                Add(pairs, [i, j]);
            fi;
        od;
    od;
    return pairs;
end;;

# One representative of each GL(d,p)-class in an ordered list.
DistinctGLClasses := function(groups, invariants, p)
    local representatives, representativeInvariants, i;
    representatives := [];
    representativeInvariants := [];
    for i in [1 .. Length(groups)] do
        if not ConjugateToSome(groups[i], invariants[i], representatives,
                               representativeInvariants, p) then
            Add(representatives, groups[i]);
            Add(representativeInvariants, invariants[i]);
        fi;
    od;
    return rec(groups := representatives,
               invariants := representativeInvariants);
end;;

# The classes in the first record which occur in none of the reference groups.
GLClassDifference := function(classes, references, referenceInvariants, p)
    local groups, invariants, i;
    groups := [];
    invariants := [];
    for i in [1 .. Length(classes.groups)] do
        if not ConjugateToSome(classes.groups[i], classes.invariants[i],
                               references, referenceInvariants, p) then
            Add(groups, classes.groups[i]);
            Add(invariants, classes.invariants[i]);
        fi;
    od;
    return rec(groups := groups, invariants := invariants);
end;;

# The number of groups in the first list that are GL(d,p)-conjugate to no
# group in the second list.  The two invariant lists only avoid impossible
# exact tests.
CountUnmatched := function(groups, invariants, reps, repInvariants, p)
    local n, i;
    n := 0;
    for i in [1 .. Length(groups)] do
        if not ConjugateToSome(groups[i], invariants[i], reps,
                               repInvariants, p) then
            n := n + 1;
        fi;
    od;
    return n;
end;;

NormalExtraspecialTypes := function(G)
    local iso, P, normalSubgroups, U, numberOfInvolutions, hasPlus, hasMinus;
    iso := IsomorphismPcGroup(G);
    P := Image(iso);
    normalSubgroups := NormalSubgroups(P);
    hasPlus := false;
    hasMinus := false;
    for U in normalSubgroups do
        if Size(U) = 32 and Size(Centre(U)) = 2
           and Size(DerivedSubgroup(U)) = 2
           and Size(FrattiniSubgroup(U)) = 2 then
            numberOfInvolutions := Number(Elements(U), u -> Order(u) = 2);
            if numberOfInvolutions = 19 then
                hasPlus := true;
            elif numberOfInvolutions = 11 then
                hasMinus := true;
            else
                Error("unexpected involution count in a normal extraspecial subgroup: ",
                      numberOfInvolutions);
            fi;
        fi;
    od;
    return [hasPlus, hasMinus];
end;;

# The record-by-record corrections quoted in the manuscript.
CheckHoltYangCorrections := function(space, coreResults, holtYangInvariants)
    local p, plusInvariants, minusInvariants, row19Groups, row19Invariants,
          row19Classes, row19PlusClasses, row19MinusClasses,
          row19PlusTypes, row19MinusTypes,
          row19PlusStructuralIndices, row19MinusStructuralIndices,
          row19PlusStructural, row19MinusStructural,
          row19FilePlusIndices, row19FileMinusIndices,
          row19FilePlus, row19FileMinus, row19StructuralUnion,
          line65Invariants, line65Classes, line65Difference,
          row65Pairs, normalTypes,
          row20Classes, row20Types, row20StructuralIndices, row20Structural,
          line20Invariants, line71Invariants, row20Extra, row20Targets,
          row20TargetInvariants, row71Classes, row105Classes,
          row71OutsideLine71, row105OutsideLine71,
          row21Classes, row21Types, row21StructuralIndices, row21Structural,
          row74Classes,
          line21Invariants, line74Invariants, row21Extra, row21Target,
          row21TargetInvariant, recordNumber;
    p := space.p;

    if space.key = "3^4" then
        RequireEqual("numbers of records in the three GF(3)^4 files",
            [Length(Line19gpsp), Length(Line19gpsm), Length(Line65gps)],
            [14, 9, 13]);
        RequireEqual("maximum orders in the two row-19 files",
            [Maximum(List(Line19gpsp, Size)),
             Maximum(List(Line19gpsm, Size))],
            [2304, 640]);
        plusInvariants := holtYangInvariants{[1 .. 14]};
        minusInvariants := holtYangInvariants{[15 .. 23]};
        RequireEqual("the six row-19 cross-file identifications",
            ExactGLConjugacyPairs(Line19gpsp, plusInvariants,
                                  Line19gpsm, minusInvariants, p),
            [[7,1], [9,9], [11,4], [12,8], [13,7], [14,3]]);

        row19Groups := Concatenation(Line19gpsp, Line19gpsm);
        row19Invariants := Concatenation(plusInvariants, minusInvariants);
        row19Classes := DistinctGLClasses(row19Groups, row19Invariants, p);
        RequireEqual("the number of distinct row-19 classes",
                     Length(row19Classes.groups), 17);
        line65Invariants := holtYangInvariants{[24 .. 36]};
        row65Pairs := ExactGLConjugacyPairs(
            Line65gps, line65Invariants,
            row19Classes.groups, row19Classes.invariants, p);
        RequireEqual("Line65 records representing row-19 classes",
            List(row65Pairs, pair -> pair[1]),
            [1, 2, 6, 9, 11, 13]);
        RequireEqual("distinct row-19 classes represented in Line65",
            Length(Set(List(row65Pairs, pair -> pair[2]))), 6);
        normalTypes := List(row19Classes.groups, NormalExtraspecialTypes);
        RequireEqual("row-19 classes containing a normal plus-type extraspecial subgroup",
                     Number(normalTypes, types -> types[1]), 13);
        RequireEqual("row-19 classes containing a normal minus-type extraspecial subgroup",
                     Number(normalTypes, types -> types[2]), 6);
        RequireEqual("row-19 classes containing cores of both types",
                     Number(normalTypes, types -> types = [true, true]), 2);
        RequireEqual("orders of the row-19 2-cores",
            SortedList(List(row19Classes.groups, G -> Size(PCore(G, 2)))),
            Concatenation(List([1 .. 15], i -> 32), [64, 64]));

        row19PlusClasses := DistinctGLClasses(coreResults[1].candidates,
                                             coreResults[1].candidateInvariants, p);
        row19MinusClasses := DistinctGLClasses(coreResults[2].candidates,
                                              coreResults[2].candidateInvariants, p);
        RequireEqual("the number of classes in the row-19 plus-type subgroup normaliser",
                     Length(row19PlusClasses.groups), 21);
        RequireEqual("the number of classes in the row-19 minus-type subgroup normaliser",
                     Length(row19MinusClasses.groups), 16);
        row19PlusTypes := List(row19PlusClasses.groups,
                              NormalExtraspecialTypes);
        row19MinusTypes := List(row19MinusClasses.groups,
                               NormalExtraspecialTypes);
        row19PlusStructuralIndices := Filtered(
            [1 .. Length(row19PlusClasses.groups)],
            i -> row19PlusTypes[i][1]);
        row19MinusStructuralIndices := Filtered(
            [1 .. Length(row19MinusClasses.groups)],
            i -> row19MinusTypes[i][2]);
        RequireEqual("row-19 plus-normaliser classes containing a normal plus-type extraspecial subgroup",
                     Length(row19PlusStructuralIndices), 13);
        RequireEqual("row-19 minus-normaliser classes containing a normal minus-type extraspecial subgroup",
                     Length(row19MinusStructuralIndices), 6);
        row19PlusStructural := rec(
            groups := row19PlusClasses.groups{row19PlusStructuralIndices},
            invariants := row19PlusClasses.invariants{row19PlusStructuralIndices});
        row19MinusStructural := rec(
            groups := row19MinusClasses.groups{row19MinusStructuralIndices},
            invariants := row19MinusClasses.invariants{row19MinusStructuralIndices});
        row19FilePlusIndices := Filtered([1 .. Length(row19Classes.groups)],
                                        i -> normalTypes[i][1]);
        row19FileMinusIndices := Filtered([1 .. Length(row19Classes.groups)],
                                         i -> normalTypes[i][2]);
        row19FilePlus := rec(
            groups := row19Classes.groups{row19FilePlusIndices},
            invariants := row19Classes.invariants{row19FilePlusIndices});
        row19FileMinus := rec(
            groups := row19Classes.groups{row19FileMinusIndices},
            invariants := row19Classes.invariants{row19FileMinusIndices});
        RequireEqual("maximum orders among the corrected row-19 types",
            [Maximum(List(row19FilePlus.groups, Size)),
             Maximum(List(row19FileMinus.groups, Size))],
            [2304, 640]);
        RequireEqual("every structural plus-type row-19 class occurs in the row-19 files",
            CountUnmatched(row19PlusStructural.groups,
                           row19PlusStructural.invariants,
                           row19FilePlus.groups, row19FilePlus.invariants, p), 0);
        RequireEqual("every plus-type row-19 file class is obtained from the plus-type normaliser",
            CountUnmatched(row19FilePlus.groups, row19FilePlus.invariants,
                           row19PlusStructural.groups,
                           row19PlusStructural.invariants, p), 0);
        RequireEqual("every structural minus-type row-19 class occurs in the row-19 files",
            CountUnmatched(row19MinusStructural.groups,
                           row19MinusStructural.invariants,
                           row19FileMinus.groups, row19FileMinus.invariants, p), 0);
        RequireEqual("every minus-type row-19 file class is obtained from the minus-type normaliser",
            CountUnmatched(row19FileMinus.groups, row19FileMinus.invariants,
                           row19MinusStructural.groups,
                           row19MinusStructural.invariants, p), 0);
        row19StructuralUnion := DistinctGLClasses(
            Concatenation(row19PlusStructural.groups,
                          row19MinusStructural.groups),
            Concatenation(row19PlusStructural.invariants,
                          row19MinusStructural.invariants), p);
        RequireEqual("the structural row-19 union has 17 classes",
                     Length(row19StructuralUnion.groups), 17);
        RequireEqual("every class in the structural row-19 union occurs in the row-19 files",
            CountUnmatched(row19StructuralUnion.groups,
                           row19StructuralUnion.invariants,
                           row19Classes.groups, row19Classes.invariants, p), 0);
        RequireEqual("every row-19 file class occurs in the structural row-19 union",
            CountUnmatched(row19Classes.groups, row19Classes.invariants,
                           row19StructuralUnion.groups,
                           row19StructuralUnion.invariants, p), 0);

        line65Classes := DistinctGLClasses(Line65gps, line65Invariants, p);
        RequireEqual("the number of distinct classes in Line65",
                     Length(line65Classes.groups), 13);
        line65Difference := GLClassDifference(
            line65Classes, row19Classes.groups, row19Classes.invariants, p);
        RequireEqual("Line65 classes which are not row-19 classes",
                     Length(line65Difference.groups), 7);
        RequireEqual("the seven other Line65 classes have no normal extraspecial subgroup of order 32",
            ForAll(line65Difference.groups,
                   G -> NormalExtraspecialTypes(G) = [false, false]), true);

        RequireEqual("extraspecial-subgroup types for Line19gpsp record 7",
            NormalExtraspecialTypes(Line19gpsp[7]), [true, true]);
        RequireEqual("extraspecial-subgroup types for Line19gpsp record 11",
            NormalExtraspecialTypes(Line19gpsp[11]), [true, true]);
        RequireEqual("extraspecial-subgroup types for Line19gpsp record 14",
            NormalExtraspecialTypes(Line19gpsp[14]), [false, true]);
        for recordNumber in [9, 12, 13] do
            RequireEqual(Concatenation("extraspecial-subgroup types for Line19gpsp record ",
                                       String(recordNumber)),
                NormalExtraspecialTypes(Line19gpsp[recordNumber]),
                [true, false]);
        od;
        RequireEqual("orders of the two both-type row-19 classes",
                     [Size(Line19gpsp[7]), Size(Line19gpsp[11])], [384, 192]);
        Print("  Row 19 has 17 classes: 13 contain a normal plus-type ",
              "extraspecial subgroup, six contain a normal minus-type ",
              "extraspecial subgroup, and two contain both.\n");
    elif space.key = "5^4" then
        line20Invariants := holtYangInvariants{[1 .. 22]};
        line71Invariants := holtYangInvariants{[23 .. 38]};
        row20Classes := DistinctGLClasses(coreResults[1].candidates,
                                         coreResults[1].candidateInvariants, p);
        RequireEqual("the number of classes in the normaliser of the row-20 prescribed subgroup",
                     Length(row20Classes.groups), 24);
        row20Types := List(row20Classes.groups, NormalExtraspecialTypes);
        row20StructuralIndices := Filtered([1 .. Length(row20Classes.groups)],
            i -> row20Types[i][1] or row20Types[i][2]);
        RequireEqual("row-20 classes containing a normal extraspecial subgroup of order 32",
                     Length(row20StructuralIndices), 22);
        row20Structural := rec(
            groups := row20Classes.groups{row20StructuralIndices},
            invariants := row20Classes.invariants{row20StructuralIndices});
        RequireEqual("every structural row-20 class occurs in Line20",
            CountUnmatched(row20Structural.groups, row20Structural.invariants,
                           Line20gps, line20Invariants, p), 0);
        RequireEqual("every Line20 class is a structural row-20 class",
            CountUnmatched(Line20gps, line20Invariants,
                           row20Structural.groups, row20Structural.invariants, p), 0);
        RequireEqual("the row-20 file occurs in that normaliser calculation",
            CountUnmatched(Line20gps, line20Invariants,
                           row20Classes.groups, row20Classes.invariants, p), 0);
        row20Extra := GLClassDifference(row20Classes, Line20gps,
                                       line20Invariants, p);
        RequireEqual("row-20 normaliser classes absent from its file",
                     Length(row20Extra.groups), 2);
        RequireEqual("the two other row-20-normaliser classes have no normal extraspecial subgroup of order 32",
            ForAll(row20Extra.groups,
                   G -> NormalExtraspecialTypes(G) = [false, false]), true);
        RequireEqual("orders of their Fitting subgroups",
            SortedList(List(row20Extra.groups, G -> Size(FittingSubgroup(G)))),
            [48, 48]);
        row20Targets := [Line71gps[10], Line71gps[16]];
        row20TargetInvariants := [line71Invariants[10], line71Invariants[16]];
        RequireEqual("orders of the two cross-row row-20 classes",
                     List(row20Targets, Size), [288, 576]);
        RequireEqual("the two row-20 classes are Line71 records 10 and 16",
            CountUnmatched(row20Extra.groups, row20Extra.invariants,
                           row20Targets, row20TargetInvariants, p), 0);
        RequireEqual("Line71 records 10 and 16 exhaust the row-20 difference",
            CountUnmatched(row20Targets, row20TargetInvariants,
                           row20Extra.groups, row20Extra.invariants, p), 0);
        RequireEqual("Line71 records 10 and 16 are absent from Line20",
            CountUnmatched(row20Targets, row20TargetInvariants,
                           Line20gps, line20Invariants, p), 2);

        row71Classes := DistinctGLClasses(coreResults[2].candidates,
                                         coreResults[2].candidateInvariants, p);
        row105Classes := DistinctGLClasses(coreResults[3].candidates,
                                          coreResults[3].candidateInvariants, p);
        RequireEqual("distinct classes obtained from row 71",
                     Length(row71Classes.groups), 23);
        RequireEqual("distinct classes obtained from row 105",
                     Length(row105Classes.groups), 23);
        RequireEqual("every Line71 class is obtained from row 71",
            CountUnmatched(Line71gps, line71Invariants,
                           row71Classes.groups, row71Classes.invariants, p), 0);
        RequireEqual("every Line71 class is obtained from row 105",
            CountUnmatched(Line71gps, line71Invariants,
                           row105Classes.groups, row105Classes.invariants, p), 0);
        row71OutsideLine71 := GLClassDifference(
            row71Classes, Line71gps, line71Invariants, p);
        row105OutsideLine71 := GLClassDifference(
            row105Classes, Line71gps, line71Invariants, p);
        RequireEqual("row-71 classes outside Line71",
                     Length(row71OutsideLine71.groups), 7);
        RequireEqual("row-105 classes outside Line71",
                     Length(row105OutsideLine71.groups), 7);
        RequireEqual("every other row-71 class occurs in Line20",
            CountUnmatched(row71OutsideLine71.groups,
                           row71OutsideLine71.invariants,
                           Line20gps, line20Invariants, p), 0);
        RequireEqual("every other row-105 class occurs in Line20",
            CountUnmatched(row105OutsideLine71.groups,
                           row105OutsideLine71.invariants,
                           Line20gps, line20Invariants, p), 0);
        RequireEqual("rows 71 and 105 give the same classes",
            CountUnmatched(row71Classes.groups, row71Classes.invariants,
                           row105Classes.groups, row105Classes.invariants, p), 0);
        RequireEqual("rows 105 and 71 give the same classes",
            CountUnmatched(row105Classes.groups, row105Classes.invariants,
                           row71Classes.groups, row71Classes.invariants, p), 0);
        Print("  Of the 24 qualifying classes in the row-20 normaliser, ",
              "exactly 22 contain a normal extraspecial subgroup of order 32; ",
              "these are the 22 Line20 classes.  The other two are Line71 ",
              "records 10 and 16, of orders 288 and 576.\n");
    elif space.key = "7^4" then
        line21Invariants := holtYangInvariants{[1 .. 16]};
        line74Invariants := holtYangInvariants{[17 .. 23]};
        RequireEqual("the cross-file identification on GF(7)^4",
            ExactGLConjugacyPairs(Line21gpsp, line21Invariants,
                                  Line74gps, line74Invariants, p), [[11,7]]);
        RequireEqual("order of the repeated GF(7)^4 class",
                     [Size(Line21gpsp[11]), Size(Line74gps[7])], [1152, 1152]);

        row74Classes := DistinctGLClasses(coreResults[3].candidates,
                                         coreResults[3].candidateInvariants, p);
        RequireEqual("distinct classes obtained from row 74",
                     Length(row74Classes.groups), 7);
        RequireEqual("every row-74 class occurs in Line74",
            CountUnmatched(row74Classes.groups, row74Classes.invariants,
                           Line74gps, line74Invariants, p), 0);
        RequireEqual("every Line74 class is obtained from row 74",
            CountUnmatched(Line74gps, line74Invariants,
                           row74Classes.groups, row74Classes.invariants, p), 0);

        row21Classes := DistinctGLClasses(coreResults[1].candidates,
                                         coreResults[1].candidateInvariants, p);
        RequireEqual("the number of classes in the row-21 plus-type subgroup normaliser",
                     Length(row21Classes.groups), 17);
        row21Types := List(row21Classes.groups, NormalExtraspecialTypes);
        row21StructuralIndices := Filtered([1 .. Length(row21Classes.groups)],
            i -> row21Types[i][1]);
        RequireEqual("row-21 classes containing a normal plus-type extraspecial subgroup of order 32",
                     Length(row21StructuralIndices), 16);
        row21Structural := rec(
            groups := row21Classes.groups{row21StructuralIndices},
            invariants := row21Classes.invariants{row21StructuralIndices});
        RequireEqual("every structural plus-type row-21 class occurs in Line21",
            CountUnmatched(row21Structural.groups, row21Structural.invariants,
                           Line21gpsp, line21Invariants, p), 0);
        RequireEqual("every Line21 class is a structural plus-type row-21 class",
            CountUnmatched(Line21gpsp, line21Invariants,
                           row21Structural.groups, row21Structural.invariants, p), 0);
        RequireEqual("the row-21 plus file occurs in that normaliser calculation",
            CountUnmatched(Line21gpsp, line21Invariants,
                           row21Classes.groups, row21Classes.invariants, p), 0);
        row21Extra := GLClassDifference(row21Classes, Line21gpsp,
                                       line21Invariants, p);
        RequireEqual("row-21 plus-type normaliser classes absent from its file",
                     Length(row21Extra.groups), 1);
        RequireEqual("the other row-21-normaliser class has no normal extraspecial subgroup of order 32",
            NormalExtraspecialTypes(row21Extra.groups[1]), [false, false]);
        row21Target := [Line74gps[4]];
        row21TargetInvariant := [line74Invariants[4]];
        RequireEqual("order of the cross-row row-21 class",
                     Size(row21Target[1]), 576);
        RequireEqual("the additional row-21 plus class is Line74 record 4",
            CountUnmatched(row21Extra.groups, row21Extra.invariants,
                           row21Target, row21TargetInvariant, p), 0);
        RequireEqual("Line74 record 4 is absent from Line21",
            CountUnmatched(row21Target, row21TargetInvariant,
                           Line21gpsp, line21Invariants, p), 1);
        Print("  Of the 17 qualifying classes in the row-21 plus-type ",
              "normaliser, exactly 16 contain a normal plus-type extraspecial ",
              "subgroup of order 32; these are the 16 Line21 classes.  The ",
              "other class is Line74 record 4.  Line21 record 11 and Line74 ",
              "record 7 represent the same class.\n");
    fi;
end;;

# Enumeration for a single prescribed subgroup.  Each calculation returns the
# order of its row-specific overgroup (nOrder), the number of subgroup classes examined
# (classCount), and the non-trivial subgroups meeting the five criteria
# (candidates); the per-space loop identifies their GL(d,p)-conjugacy classes
# across all prescribed subgroups on the space.

# The direct method enumerates every conjugacy class of subgroups of the
# row-specific overgroup N, and then applies the five criteria.  In the ordinary
# rows N is the full normaliser in GL(d,p); in a semilinear row it is the
# covering group in GammaL(e,p^a) supplied by the structural reduction.  The
# list is larger than the set required: a subgroup need not contain the
# prescribed subgroup, and the same GL(d,p)-class can arise from different
# prescribed subgroups.  Exact GL(d,p)-conjugacy is used afterwards to remove
# repetitions.
DirectCoreCandidates := function(core, p, d)
    local cn, classes, candidates, normaliserSolvable, cl, G;
    cn := CoreDataForMethod(core);
    if core.method = "multiplicity-direct" then
        CertifyMultiplicityNormaliser(core, cn, p, d);
    elif core.method = "semilinear-direct" then
        CertifySemilinearNormaliser(core, cn, p, d);
    fi;
    classes := ConjugacyClassesSubgroups(cn.N);
    normaliserSolvable := IsSolvableGroup(cn.N);
    candidates := [];
    for cl in classes do
        G := Representative(cl);
        if not IsTrivial(G)
           and SatisfiesSmallSpaceCriteria(G, p, d,
                                           normaliserSolvable) then
            Add(candidates, G);
        fi;
    od;
    return rec(nOrder := Size(cn.N), classCount := Length(classes),
               candidates := candidates, coreGroup := cn.E,
               normaliser := cn.N, allSubgroupsCovered := true);
end;;

# The structural theorem supplies a distinguished extraspecial subgroup E0
# which is normal in every qualifying group.  In the symplectic-type case E0
# has index two in S=<E0,iI>.  The program lists
# every extraspecial subgroup of index two in S before taking orbits under the
# relevant overgroup.  The two orbits are the plus and minus types.  It then
# normalises one representative of each type and enumerates every solvable
# subgroup of N(E0)/E0.
# This covers groups with O_2(G)=S and groups with O_2(G)=E0.  Exact
# GL(d,p)-conjugacy is used afterwards only to identify repetitions, not to
# justify the coverage.
QuotientCoreCandidates := function(core, p, d)
    local cn, S, N, extraspecials, reps, E0, U, M, quo, Q, classes, candidates,
          classCount, Hbar, H, fullN, fullM, scalar, involutionCounts;
    cn := CoreDataForMethod(core);
    S := cn.E;
    N := cn.N;
    if core.method = "semilinear-quotient" then
        CertifySemilinearNormaliser(core, cn, p, d);
    elif core.method = "multiplicity-quotient" then
        CertifyMultiplicityNormaliser(core, cn, p, d);
    fi;
    if core.kind = "S" then
        if core.method <> "semilinear-quotient"
           and core.method <> "multiplicity-quotient" then
            fullN := Normalizer(GL(d, p), S);
            RequireEqual(Concatenation("constructed full normaliser of the prescribed subgroup for row ",
                                    core.row), N, fullN);
        fi;
        scalar := Z(p)^((p-1)/4) * IdentityMat(d, GF(p));
        RequireEqual(Concatenation("fourth-root scalar lies in S for row ",
                                core.row), scalar in S, true);
        extraspecials := Filtered(MaximalSubgroups(S),
            U -> Size(Centre(U)) = 2 and Size(DerivedSubgroup(U)) = 2
                 and Size(U) = PrimePowerData(core.e).r ^
                               (1 + 2 * PrimePowerData(core.e).n));
        RequireEqual(Concatenation("extraspecial subgroups of index two in S for row ",
                                core.row), Length(extraspecials), core.e ^ 2);
        reps := [];
        for E0 in extraspecials do
            if ForAll(reps, U -> RepresentativeAction(N, U, E0) = fail) then
                Add(reps, E0);
            fi;
        od;
        RequireEqual(Concatenation("two conjugacy classes of extraspecial subgroups for row ",
                                core.row), Length(reps), 2);
        involutionCounts := SortedList(List(reps,
            E0 -> Number(Elements(E0), x -> Order(x) = 2)));
        RequireEqual(Concatenation("plus and minus extraspecial types for row ",
                                core.row), involutionCounts,
                     [core.e ^ 2 - core.e - 1,
                      core.e ^ 2 + core.e - 1]);
        RequireEqual(Concatenation("S=<E0,iI> for row ", core.row),
          ForAll(reps, E0 -> ClosureGroup(E0, Group(scalar)) = S), true);
    else
        reps := [S];
    fi;
    candidates := [];
    classCount := 0;
    for E0 in reps do
        M := Normalizer(N, E0);
        if core.method = "semilinear-quotient"
           or core.method = "multiplicity-quotient" then
            RequireEqual(Concatenation("extraspecial subgroup is normal in its ",
                                    "row-specific normaliser for row ",
                                    core.row), IsNormal(M, E0), true);
        else
            fullM := Normalizer(GL(d, p), E0);
            RequireEqual(Concatenation("full extraspecial normaliser for row ",
                                    core.row), M, fullM);
        fi;
        quo := NaturalHomomorphismByNormalSubgroup(M, E0);
        Q := Image(quo);
        classes := List(ConjugacyClassesSubgroups(Q), Representative);
        if not IsSolvableGroup(Q) then
            classes := Filtered(classes, IsSolvableGroup);
        fi;
        classCount := classCount + Length(classes);
        for Hbar in classes do
            H := PreImage(quo, Hbar);
            if SatisfiesSmallSpaceCriteria(H, p, d, true) then
                Add(candidates, H);
            fi;
        od;
    od;
    return rec(nOrder := Size(N), classCount := classCount,
               candidates := candidates, coreGroup := S,
               normaliser := N, allSubgroupsCovered := false);
end;;

# Row 112 has a three-dimensional multiplicity action.  Quasiprimitivity
# forces that action to be irreducible and solvable.  IrredSol supplies all 22
# GL(3,5)-classes of such multiplicity groups.  Within each resulting group M,
# every qualifying group normalises an extraspecial subgroup E0 of the local
# symplectic-type subgroup.  The two M-orbits of E0 cover both possible
# O_2-types, exactly as in the other normaliser-quotient calculations.
# We therefore enumerate solvable subgroup classes of N_M(E0)/E0, rather than
# the many subgroups of M which do not contain a prescribed extraspecial subgroup.
Row112Candidates := function(core, p, d)
    local F, normaliserData, inflatedLocal, inflatedCore, scalar,
          extraspecials, groups, candidates, candidateInvariants, classCount,
          C, gens, B, M, reps, E0, U, extraspecialNormaliser, quo, Q,
          classes, Hbar, H,
          invariant;
    F := GF(5);
    normaliserData := MultiplicityCoreData(core);
    CertifyMultiplicityNormaliser(core, normaliserData, p, d);
    inflatedLocal := GeneratorsOfGroup(normaliserData.localAction);
    inflatedCore := normaliserData.E;
    scalar := Z(5) * IdentityMat(6, F);
    RequireEqual("fourth-root scalar lies in the prescribed row-112 symplectic-type subgroup",
              scalar in inflatedCore, true);
    extraspecials := Filtered(MaximalSubgroups(inflatedCore),
        E0 -> Size(E0) = 8 and Size(Centre(E0)) = 2
              and Size(DerivedSubgroup(E0)) = 2);
    groups := AllIrreducibleSolubleMatrixGroups(Degree, 3, Field, F);
    RequireEqual("number of irreducible solvable multiplicity groups for row 112",
              Length(groups), 22);
    candidates := [];
    candidateInvariants := [];
    classCount := 0;
    for C in groups do
        gens := ShallowCopy(inflatedLocal);
        for B in GeneratorsOfGroup(C) do
            Add(gens, InflateMultiplicityMatrix(B, 2, F));
        od;
        M := Group(gens);
        RequireEqual("the row-112 symplectic-type subgroup is normal in M",
                  IsNormal(M, inflatedCore), true);
        reps := [];
        for E0 in extraspecials do
            if ForAll(reps, U -> RepresentativeAction(M, U, E0) = fail) then
                Add(reps, E0);
            fi;
        od;
        RequireEqual("two M-orbits of extraspecial subgroups in row 112",
                  Length(reps), 2);
        RequireEqual("the row-112 symplectic-type subgroup is generated by E0 and the scalar",
          ForAll(reps,
                 E0 -> ClosureGroup(E0, Group(scalar)) = inflatedCore), true);
        for E0 in reps do
            extraspecialNormaliser := Normalizer(M, E0);
            RequireEqual("the row-112 extraspecial subgroup is normal in its normaliser in M",
                      IsNormal(extraspecialNormaliser, E0), true);
            quo := NaturalHomomorphismByNormalSubgroup(
                extraspecialNormaliser, E0);
            Q := Image(quo);
            RequireEqual("the row-112 quotient is solvable",
                         IsSolvableGroup(Q), true);
            classes := List(ConjugacyClassesSubgroups(Q), Representative);
            classCount := classCount + Length(classes);
            for Hbar in classes do
                H := PreImage(quo, Hbar);
                if SatisfiesRow112Criteria(H, p, d) then
                    invariant := CharacteristicPolynomialConjugacyInvariant(H);
                    if ForAll([1 .. Length(candidates)],
                              i -> candidateInvariants[i] <> invariant
                                   or not AreConjugateInGL(
                                       H, candidates[i], p)) then
                        Add(candidates, H);
                        Add(candidateInvariants, invariant);
                    fi;
                fi;
            od;
        od;
    od;
    return rec(nOrder := Size(normaliserData.N), classCount := classCount,
               candidates := candidates, coreGroup := fail,
               normaliser := fail, allSubgroupsCovered := false);
end;;

RequireCompleteSubgroupEnumeration := function(core, sourceResult)
    if not IsBound(sourceResult.allSubgroupsCovered)
       or sourceResult.allSubgroupsCovered <> true then
        Error("The calculation used to cover row ", core.row,
              " did not cover every subgroup of its normaliser.");
    fi;
end;;

# If a conjugate of one full normaliser lies in a normaliser whose subgroup
# classes have all been examined, every group arising from the first
# normaliser has already occurred in the second calculation.
ContainedCoreCertificate := function(core, sourceResult, p, d)
    local target, embedding;
    RequireCompleteSubgroupEnumeration(core, sourceResult);
    RequireEqual(Concatenation("dimension for the local normaliser inclusion in row ",
                            core.row), d, 2);
    target := CoreAndNormaliser(core);
    embedding := LocalPlusNormaliserEmbedding(
        p, sourceResult.coreGroup, sourceResult.normaliser);
    RequireEqual(Concatenation("standard plus-type subgroup for row ", core.row),
                 target.E, embedding.core);
    RequireEqual(Concatenation("full plus-type normaliser for row ", core.row),
                 target.N, embedding.normaliser);
    return rec(nOrder := Size(target.N), classCount := 0, candidates := [],
               coreGroup := target.E, normaliser := target.N,
               allSubgroupsCovered := true);
end;;

ContainedMultiplicityCoreCertificate := function(core, sourceResult, p, d)
    local target, minusCore, expectedMinus, F, pp, localMinus,
          localMinusNormaliser, embedding, conjugator;
    RequireCompleteSubgroupEnumeration(core, sourceResult);
    target := MultiplicityCoreData(core);
    CertifyMultiplicityNormaliser(core, target, p, d);
    minusCore := ShallowCopy(core);
    minusCore.kind := "E-";
    expectedMinus := ParametricCore(minusCore);
    RequireEqual(Concatenation("minus-type subgroup used to cover row ", core.row),
                 sourceResult.coreGroup, expectedMinus);
    F := GF(p);
    pp := PrimePowerData(core.e);
    localMinus := Group(List(CoreGeneratorsOverField(p, pp, "E-"),
                             A -> One(F) * A));
    localMinusNormaliser := Normalizer(GL(core.e, p), localMinus);
    embedding := LocalPlusNormaliserEmbedding(
        p, localMinus, localMinusNormaliser);
    RequireEqual(Concatenation("local plus-type subgroup for row ", core.row),
                 target.localCore, embedding.core);
    RequireEqual(Concatenation("local plus-type normaliser for row ", core.row),
                 target.localNormaliser, embedding.normaliser);
    conjugator := InflateLocalMatrix(embedding.conjugator, core.b, F);
    RequireEqual(Concatenation("rank of the normaliser-inclusion conjugator for row ",
                            core.row), RankMat(conjugator), d);
    RequireEqual(Concatenation("plus-type normaliser contained in the earlier ",
                            "minus-type normaliser for row ", core.row),
                 IsSubgroup(sourceResult.normaliser,
                            target.N ^ conjugator), true);
    return rec(nOrder := Size(target.N), classCount := 0, candidates := [],
               coreGroup := target.E, normaliser := target.N,
               allSubgroupsCovered := true);
end;;

DuplicateCoreCertificate := function(core, sourceResult, p, d)
    local target, iso, gens, imgs, x, targetN;
    RequireCompleteSubgroupEnumeration(core, sourceResult);
    target := ParametricCore(core);
    iso := IsomorphismGroups(sourceResult.coreGroup, target);
    RequireEqual(Concatenation("abstract isomorphism between prescribed subgroups for row ", core.row),
              iso <> fail, true);
    gens := GeneratorsOfGroup(sourceResult.coreGroup);
    imgs := List(gens, g -> Image(iso, g));
    x := MTX.IsomorphismModules(GModuleByMats(gens, GF(p)),
                               GModuleByMats(imgs, GF(p)));
    RequireEqual(Concatenation("linear conjugator between prescribed subgroups for row ", core.row),
              x <> fail, true);
    RequireEqual(Concatenation("full rank of the subgroup conjugator for row ",
                            core.row), RankMat(x), d);
    RequireEqual(Concatenation("generator equations for row ", core.row),
      ForAll([1 .. Length(gens)],
             i -> x^-1 * gens[i] * x = imgs[i]), true);
    RequireEqual(Concatenation("prescribed-subgroup equality after conjugation for row ", core.row),
              sourceResult.coreGroup ^ x, target);
    # Conjugation carries the full normaliser of the source subgroup onto the
    # full normaliser of the target subgroup.
    targetN := sourceResult.normaliser ^ x;
    RequireEqual(Concatenation("conjugated normaliser contains the prescribed ",
                            "subgroup normally for row ", core.row),
                 IsNormal(targetN, target), true);
    RequireEqual(Concatenation("order preserved under normaliser conjugacy for row ",
                            core.row), Size(targetN),
                 Size(sourceResult.normaliser));
    return rec(nOrder := Size(targetN), classCount := 0, candidates := [],
               coreGroup := target, normaliser := targetN,
               allSubgroupsCovered := true);
end;;

CoreCandidates := function(core, p, d, priorResults)
    if core.method = "quotient"
       or core.method = "semilinear-quotient"
       or core.method = "multiplicity-quotient" then
        return QuotientCoreCandidates(core, p, d);
    fi;
    if core.method = "row112" then
        return Row112Candidates(core, p, d);
    fi;
    if core.method = "contained" then
        return ContainedCoreCertificate(
            core, priorResults[core.coveredByIndex], p, d);
    fi;
    if core.method = "multiplicity-contained" then
        return ContainedMultiplicityCoreCertificate(
            core, priorResults[core.coveredByIndex], p, d);
    fi;
    if core.method = "duplicate" then
        return DuplicateCoreCertificate(core,
                                        priorResults[core.duplicateIndex], p, d);
    fi;
    return DirectCoreCandidates(core, p, d);
end;;

RunOneSpace := function(space)
    local p, d, acceptedReps, acceptedInvariants, totalClasses,
          normaliserOrders, priorResults, core, coreResult, G, invariant,
          holtYangGroups, name, holtYangInvariants, additionalClasses,
          unrecoveredHoltYangClasses,
          agree;
    p := space.p;
    d := space.d;
    acceptedReps := [];
    acceptedInvariants := [];
    totalClasses := 0;
    normaliserOrders := [];
    priorResults := [];
    Print("GF(", p, ")^", d, ":\n");
    for core in space.cores do
        coreResult := CoreCandidates(core, p, d, priorResults);
        Add(priorResults, coreResult);
        coreResult.candidateInvariants := [];
        RequireEqual(Concatenation("order of the row-specific overgroup in GL(",
                                 String(d), ",", String(p), ") for row ",
                                 core.row),
                  coreResult.nOrder, core.nOrder);
        RequireEqual(Concatenation("enumerated class count for row ", core.row),
                   coreResult.classCount, core.classCount);
        RequireEqual(Concatenation("qualifying groups before GL-conjugacy comparisons for row ",
                                core.row),
                   Length(coreResult.candidates), core.acceptedCount);
        if core.method = "row112" then
            Print("  Row 112: the prescribed-subgroup normaliser in GL(",
                  d, ",", p, ") has order ", coreResult.nOrder, "; the 44 ",
                  "normaliser quotients contain ", coreResult.classCount,
                  " solvable subgroup classes in total and yield ",
                  Length(coreResult.candidates), " qualifying groups.\n");
        elif core.method = "semilinear-direct" then
            Print("  Row ", core.row,
                  ": the row-specific semilinear overgroup has order ",
                  coreResult.nOrder, ".  All ", coreResult.classCount,
                  " of its subgroup classes are examined; the five tests retain ",
                  Length(coreResult.candidates), " qualifying groups.\n");
        elif core.method = "direct" or
             core.method = "multiplicity-direct" then
            Print("  Row ", core.row,
                  ": the full prescribed-subgroup normaliser in GL(", d,
                  ",", p, ") has order ", coreResult.nOrder, ".  All ",
                  coreResult.classCount,
                  " of its subgroup classes are examined; the five tests retain ",
                  Length(coreResult.candidates), " qualifying groups.\n");
        elif core.method = "duplicate" then
            Print("  Row ", core.row,
                  ": its prescribed subgroup and normaliser are conjugate ",
                  "to those of the earlier row recorded above, so no second ",
                  "enumeration is needed.\n");
        elif core.method = "contained"
             or core.method = "multiplicity-contained" then
            Print("  Row ", core.row,
                  ": a conjugate of its full plus-type normaliser, of order ",
                  coreResult.nOrder, ", lies in the minus-type normaliser ",
                  "examined above, so all its subgroup classes have already ",
                  "been considered.\n");
        elif core.method = "semilinear-quotient" then
            Print("  Row ", core.row,
                  ": the row-specific semilinear overgroup has order ",
                  coreResult.nOrder, "; the quotient calculations examine ",
                  coreResult.classCount,
                  " solvable subgroup classes and yield ",
                  Length(coreResult.candidates), " qualifying groups.\n");
        else
            Print("  Row ", core.row,
                  ": the prescribed-subgroup normaliser in GL(", d, ",", p,
                  ") has order ", coreResult.nOrder, "; the normaliser-quotient ",
                  "calculations examine ", coreResult.classCount,
                  " solvable subgroup classes and yield ",
                  Length(coreResult.candidates), " qualifying groups.\n");
        fi;
        Add(normaliserOrders, coreResult.nOrder);
        totalClasses := totalClasses + coreResult.classCount;
        for G in coreResult.candidates do
            invariant := CharacteristicPolynomialConjugacyInvariant(G);
            Add(coreResult.candidateInvariants, invariant);
            if not ConjugateToSome(G, invariant, acceptedReps,
                                   acceptedInvariants, p) then
                Add(acceptedReps, G);
                Add(acceptedInvariants, invariant);
            fi;
        od;
    od;
    holtYangGroups := [];
    for name in space.holtYangFiles do
        Append(holtYangGroups, ValueGlobal(name));
    od;
    RequireEqual(Concatenation("number of Holt--Yang groups on GF(", String(p),
                            ")^", String(d)),
              Length(holtYangGroups), space.listed);
    holtYangInvariants := List(holtYangGroups,
                              CharacteristicPolynomialConjugacyInvariant);
    CheckHoltYangCorrections(space, priorResults, holtYangInvariants);

    additionalClasses := CountUnmatched(acceptedReps, acceptedInvariants,
                                        holtYangGroups,
                                        holtYangInvariants, p);
    unrecoveredHoltYangClasses := CountUnmatched(
        holtYangGroups, holtYangInvariants,
        acceptedReps, acceptedInvariants, p);
    agree := (additionalClasses = 0 and unrecoveredHoltYangClasses = 0);
    RequireEqual(Concatenation("distinct enumerated classes on GF(", String(p),
                            ")^", String(d)),
              Length(acceptedReps), space.distinct);
    RequireEqual(Concatenation("enumerated classes absent from the Holt--Yang data on GF(",
                            String(p), ")^", String(d)),
                 additionalClasses, 0);
    RequireEqual(Concatenation("Holt--Yang classes not recovered on GF(",
                            String(p), ")^", String(d)),
                 unrecoveredHoltYangClasses, 0);
    RequireEqual(Concatenation("agreement with the Holt--Yang list on ",
                            space.key), agree, true);
    Print("  These give ", Length(acceptedReps),
          " distinct GL(", d, ",", p,
           ")-classes, exactly the number represented by the corresponding ",
          "Holt--Yang files.\n");
    return rec(key := space.key,
               rows := List(space.cores, core -> core.row),
               enumeratedClasses := totalClasses,
               normaliserOrders := normaliserOrders,
               distinct := Length(acceptedReps),
               holtYangRecords := Length(holtYangGroups));
end;;

smallSpaceResults := List(Spaces, RunOneSpace);;
RequireEqual("number of completed spaces", Length(smallSpaceResults), 20);

Print("All 48 row-and-type calculations, covering 36 parameter rows on the ",
      "twenty small spaces treated here, have been completed; the per-space ",
      "unions agree exactly with the classes represented by the corresponding ",
      "Holt--Yang files.\n");
QUIT_GAP(0);
