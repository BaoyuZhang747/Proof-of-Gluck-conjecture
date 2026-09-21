# Exhaustive calculation for the plus-type extraspecial subgroup E on GF(3)^16.

SetPrintFormattingStatus("*stdout*", false);;
Read("matrix_group_tests.g");;
Read("gf3_16_extraspecial_quotients.g");;
Read("gf3_16_projective_orbits.g");;
Read("gf3_16_extraspecial_plus_generators.g");;
Read("gf3_16_plus_data.g");;

F3 := GF(3);;
F2 := GF(2);;
one3 := One(F3);;
one2 := One(F2);;
I16 := IdentityMat(16, F3);;
coreGens := List(CoreGeneratorMatrices,
    m -> List(m, row -> List(row, x -> x * one3)));;
Ecore := Group(coreGens);;

Assert(0, Size(Ecore) = 512);;
Assert(0, Size(Centre(Ecore)) = 2);;
Assert(0, Set(Elements(Centre(Ecore))) = Set([ I16, -I16 ]));;
Assert(0, Number(Elements(Ecore), x -> Order(x) = 2) = 271);;
Assert(0, MTX.IsIrreducible(GModuleByMats(coreGens, F3)));;
Assert(0, IsSolvableGroup(Ecore));;
Assert(0, not IsMetacyclicSolvableGroup(Ecore));;
coreCentraliser := FullMatrixAlgebraCentralizer(F3, coreGens);;
Assert(0, Dimension(coreCentraliser) = 1);;

# The centraliser consists of the scalars, and every central automorphism of an
# extraspecial group is inner.  Hence the kernel of the normaliser action on
# E/Z(E) is E.  For each generator of the orthogonal quotient, the data give
# both its action on E/Z(E) and a lifting matrix in GL(16,3).  The checks below
# verify the pairing, and these matrices generate the full orthogonal quotient.

GF316Bits8 := function(n)
    local bits, k, power;
    bits := [];;
    for k in [1 .. 8] do
        power := 2^(8 - k);;
        if n >= power then
            Add(bits, 1);;
            n := n - power;
        else
            Add(bits, 0);
        fi;
    od;
    return bits;
end;;

GF316CoreWord := function(bits)
    local word, i;
    word := I16;;
    for i in [1 .. 8] do
        if not IsZero(bits[i]) then
            word := word * coreGens[i];
        fi;
    od;
    return word;
end;;

quotientMats := [];;
quotientBits := [];;
for n in [0 .. 255] do
    bits := GF316Bits8(n);;
    word := GF316CoreWord(bits);;
    Add(quotientMats, word);;
    Add(quotientBits, List(bits, x -> x * one2));;
    Add(quotientMats, -word);;
    Add(quotientBits, List(bits, x -> x * one2));;
od;

GF316InducedMatrix := function(t)
    local columns, j, image, position, rows, r, c;
    columns := [];;
    for j in [1 .. 8] do
        image := t^-1 * coreGens[j] * t;;
        position := Position(quotientMats, image);;
        if position = fail then
            return fail;
        fi;
        Add(columns, quotientBits[position]);
    od;
    rows := [];;
    for r in [1 .. 8] do
        Add(rows, List([1 .. 8], c -> columns[c][r]));
    od;
    return rows;
end;;

actionMatrices := GF316PlusData.actionMatrices;;
lifts := GF316PlusData.liftMatrices;;
Assert(0, Length(actionMatrices) = Length(lifts));;
Assert(0, ForAll([1 .. Length(lifts)], i ->
    TransposedMat(GF316InducedMatrix(lifts[i])) = actionMatrices[i]));;
Assert(0, ForAll([1 .. Length(lifts)], i ->
    ForAll(AsList(F2^8), v ->
        quotientBits[Position(quotientMats,
            lifts[i]^-1 * GF316CoreWord(List(v, IntFFE)) * lifts[i])]
            = v * actionMatrices[i])));;
Q := Group(actionMatrices);;
Assert(0, Size(Q) = 348364800);;

Print("The plus-type extraspecial subgroup E has order 512, and ",
    "the quotient of its normaliser in GL(16,3) by E has order ",
    Size(Q), ".\n");;

freeQ := FreeGroup(Length(actionMatrices));;
freeQGens := GeneratorsOfGroup(freeQ);;
epiQ := GroupHomomorphismByImages(freeQ, Q, freeQGens, actionMatrices);;
Assert(0, epiQ <> fail and Image(epiQ) = Q);;

GF316LiftQElement := function(q)
    local word;
    word := PreImagesRepresentative(epiQ, q);;
    if word = fail then
        Error("a quotient element has no word in the chosen generators");
    fi;
    return MappedWord(word, freeQGens, lifts);
end;;

GF316LiftQSubgroup := function(K)
    local quotientGenerators, liftedGenerators, i;
    quotientGenerators := GeneratorsOfGroup(K);;
    liftedGenerators := List(quotientGenerators, GF316LiftQElement);;
    for i in [1 .. Length(quotientGenerators)] do
        Assert(0, TransposedMat(
            GF316InducedMatrix(liftedGenerators[i])) = quotientGenerators[i]);
    od;
    return Group(Concatenation(coreGens, liftedGenerators));
end;;

screen := GF316QuasiprimitiveQuotients(1, Q, coreGens,
    GF316LiftQSubgroup, 19750, 19391, 567, 567);;
Print("GO+(8,2) has ", screen.subgroupClassCount,
    " subgroup classes, of which ", screen.solvableClassCount,
    " are solvable.\n");;
Print("The quadratic-form test on invariant subspaces of E/Z(E) retains ",
    screen.correctedCoreNormalCount, " classes; all ", screen.exactCount,
    " are irreducible and quasiprimitive.\n");;

# A vector with nontrivial E-stabiliser cannot be regular for H.  On an
# E/Z(E)-orbit of projective points with trivial stabiliser, the stabiliser in H
# of a representative vector maps isomorphically onto the stabiliser in K=H/E
# of that E/Z(E)-orbit.  For an element of this latter stabiliser, first multiply
# a lift by the unique element of E that returns its image line to the original
# line, and then by z=-I if necessary.  Thus H has a regular vector orbit exactly
# when K has a regular orbit on the E/Z(E)-orbits with trivial stabiliser below.

projectiveAction := GF316ProjectiveRegularCoreAction(coreGens,
    actionMatrices, lifts);;
Assert(0, projectiveAction.lineCount = 21523360);;
Assert(0, projectiveAction.projectiveOrbitCount = 87535);;
Assert(0, projectiveAction.regularCoreOrbitCount = 81640);;
Assert(0, Size(projectiveAction.quotientImage) = Size(Q));;
Print("The ", projectiveAction.lineCount,
    " projective points form ", projectiveAction.projectiveOrbitCount,
    " E/Z(E)-orbits; ", projectiveAction.regularCoreOrbitCount,
    " have trivial point stabiliser.\n");;
Print("The induced action on the E/Z(E)-orbits with trivial point ",
    "stabiliser is faithful, with image order ",
    Size(projectiveAction.quotientImage), ".\n");;

regularCount := 0;;
exceptions := [];;
for r in screen.survivors do
    Kimage := Image(projectiveAction.quotientHomomorphism, r.quotient);;
    Assert(0, Size(Kimage) = r.quotientOrder);;
    quotientOrbits := OrbitsDomain(Kimage,
        [1 .. projectiveAction.regularCoreOrbitCount]);;
    regularOrbit := First(quotientOrbits,
        orbit -> Length(orbit) = r.quotientOrder);;
    if regularOrbit = fail then
        Add(exceptions, r);
    else
        regularCount := regularCount + 1;;
        r.regularVector :=
            projectiveAction.regularCoreRepresentatives[regularOrbit[1]];;
    fi;
    Unbind(quotientOrbits);;
od;
Assert(0, regularCount = 555);;
Assert(0, Length(exceptions) = 12);;
Assert(0, ForAll(exceptions,
    r -> Size(PCore(r.quotient, 2)) = 1));;
Print("Of the 567 lifts, ", regularCount,
    " have a regular orbit and ", Length(exceptions), " do not.\n");;

# Identify the twelve exceptions with the twelve Holt--Yang groups.  The data
# contain quotient subgroup representatives and explicit change-of-basis
# matrices.  Conjugacy in the quotient is decided independently here.  Despite
# the letter m in the historical filename Line1gpsm.g, the prescribed
# extraspecial subgroup in each of its twelve records is of plus type.

Read("holt_yang_data/Line1gpsm.g");;
Assert(0, Length(Line1gps) = 12);;
references := GF316PlusData.referenceData;;
Assert(0, List(references, r -> r.holtYangRecord) = [1 .. 12]);;
for reference in references do
    reference.quotient := Group(reference.quotientGenerators);;
    Assert(0, IsSubgroup(Q, reference.quotient));;
    Assert(0, Size(reference.quotient) = reference.quotientOrder);;
    Assert(0, GF316LiftQSubgroup(reference.quotient)
        ^ reference.conjugator = Line1gps[reference.holtYangRecord]);
od;

quotientToPerm := IsomorphismPermGroup(Q);;
Pquotient := Image(quotientToPerm);;
usedReferences := BlistList([1 .. 12], []);;
for r in exceptions do
    Kpermutation := Image(quotientToPerm, r.quotient);;
    choices := [];;
    for i in [1 .. 12] do
        if not usedReferences[i]
           and references[i].quotientOrder = r.quotientOrder then
            referencePermutation := Image(quotientToPerm,
                references[i].quotient);;
            conjugatorPermutation := RepresentativeAction(Pquotient,
                Kpermutation, referencePermutation);;
            if conjugatorPermutation <> fail then
                Add(choices, [ i, conjugatorPermutation ]);
            fi;
        fi;
    od;
    Assert(0, Length(choices) = 1);;
    i := choices[1][1];;
    usedReferences[i] := true;;
    conjugatorQ := PreImagesRepresentative(quotientToPerm, choices[1][2]);;
    Assert(0, r.quotient^conjugatorQ = references[i].quotient);;
    lift := GF316LiftQElement(conjugatorQ);;
    G := GF316LiftQSubgroup(r.quotient);;
    referenceGroup := GF316LiftQSubgroup(references[i].quotient);;
    Assert(0, G^lift = referenceGroup);;
    Assert(0, G^(lift * references[i].conjugator)
        = Line1gps[references[i].holtYangRecord]);;
od;
Assert(0, ForAll(usedReferences, x -> x));;
Print("The twelve groups without a regular orbit are exactly the twelve ",
    "Holt--Yang GF(3)^16 plus-type groups.\n");;
QUIT_GAP(0);
