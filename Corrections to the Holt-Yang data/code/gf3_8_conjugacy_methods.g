# Exact matrix-group operations for the GF(3)^8 comparison.

SetPrintFormattingStatus("*stdout*", false);;

GF38Stop := function(message)
    Error("GF(3)^8 conjugacy check: ", message);
end;;

GF38Check := function(condition, message)
    if not condition then
        GF38Stop(message);
    fi;
end;;

GF38RequireAndRead := function(path)
    if not IsReadableFile(path) then
        GF38Stop(Concatenation("required input is missing or unreadable: ", path));
    fi;
    Read(path);
end;;

# Check the representation assumptions needed by the exact test, and rebuild
# the group to verify its recorded order.
GF38MatrixGroupFromGenerators := function(gens, p, d, expectedOrder, label)
    local m, row, x, G, M;
    GF38Check(IsList(gens) and Length(gens) > 0,
             Concatenation(label, ": empty or non-list generator set"));
    for m in gens do
        GF38Check(IsList(m) and Length(m) = d,
                 Concatenation(label, ": generator is not a ", String(d),
                               " by ", String(d), " matrix"));
        for row in m do
            GF38Check(IsList(row) and Length(row) = d,
                     Concatenation(label, ": malformed matrix row"));
            for x in row do
                GF38Check(x in GF(p),
                         Concatenation(label, ": matrix entry is not in GF(",
                                       String(p), ")"));
            od;
        od;
        GF38Check(DeterminantMat(m) <> Zero(GF(p)),
                 Concatenation(label, ": singular alleged generator"));
    od;
    G := Group(gens);
    GF38Check(Size(G) = expectedOrder,
             Concatenation(label, ": rebuilt order ", String(Size(G)),
                           " differs from recorded order ",
                           String(expectedOrder)));
    GF38Check(IsSolvableGroup(G),
             Concatenation(label, ": group is not solvable"));
    M := GModuleByMats(GeneratorsOfGroup(G), GF(p));
    GF38Check(MTX.Dimension(M) = d,
             Concatenation(label, ": module has the wrong dimension"));
    GF38Check(MTX.IsIrreducible(M),
             Concatenation(label, ": natural module is not irreducible"));
    return G;
end;;

# Necessary invariant only.  Equality is never treated as a positive answer.
GF38ClassInvariant := function(G)
    local iso, P, classes;
    iso := IsomorphismPcGroup(G);
    P := Image(iso);
    classes := ConjugacyClasses(P);
    return [ Size(G),
             SortedList(List(classes, c ->
                 [ Size(c),
                   CoefficientsOfUnivariatePolynomial(
                       CharacteristicPolynomial(
                           PreImagesRepresentative(iso,
                                                   Representative(c)))) ])) ];
end;;

GF38ExactContext := function(G)
    local iso, P;
    iso := IsomorphismPcGroup(G);
    P := Image(iso);
    return rec(group := G,
               order := Size(G),
               iso := iso,
               pc := P,
               pcgens := GeneratorsOfGroup(P),
               comparisonResults := [],
               firstArgumentReady := false);
end;;

GF38PrepareFirstArgument := function(ctx, p)
    local A, inner;
    if ctx.firstArgumentReady then
        return;
    fi;
    A := AutomorphismGroup(ctx.pc);
    inner := InnerAutomorphismsAutomorphismGroup(A);
    ctx.outerTransversal := List(RightCosets(A, inner), Representative);
    ctx.module := GModuleByMats(
        List(ctx.pcgens, x -> PreImagesRepresentative(ctx.iso, x)), GF(p));
    ctx.firstArgumentReady := true;
end;;

# Exact GL(d,p)-conjugacy, returning and independently checking a conjugating
# matrix.  If the returned record has isConjugate=true, its field
# conjugatingMatrixAtoB is a matrix X satisfying X^-1 A X=B.
GF38ExactConjugacyByAutomorphisms := function(ctxA, ctxB, p)
    local phi, alpha, imgs, Mh, X, i, Agens, conjugated, tested;
    if ctxA.order <> ctxB.order then
        return rec(isConjugate := false, outerCosetsTested := 0);
    fi;
    phi := IsomorphismGroups(ctxA.pc, ctxB.pc);
    if phi = fail then
        return rec(isConjugate := false, outerCosetsTested := 0);
    fi;
    GF38PrepareFirstArgument(ctxA, p);
    Agens := List(ctxA.pcgens,
                  x -> PreImagesRepresentative(ctxA.iso, x));
    tested := 0;
    for alpha in ctxA.outerTransversal do
        tested := tested + 1;
        imgs := List(ctxA.pcgens, x ->
            PreImagesRepresentative(ctxB.iso,
                Image(phi, Image(alpha, x))));
        Mh := GModuleByMats(imgs, GF(p));
        X := MTX.IsomorphismModules(ctxA.module, Mh);
        if X <> fail then
            GF38Check(Length(X) = Length(X[1]) and RankMat(X) = Length(X),
                     "MeatAxe returned a non-invertible module isomorphism");
            for i in [1 .. Length(Agens)] do
                GF38Check(X^-1 * Agens[i] * X = imgs[i],
                         "MeatAxe conjugating matrix failed a generator intertwining check");
            od;
            conjugated := Group(List(GeneratorsOfGroup(ctxA.group),
                                      g -> X^-1 * g * X));
            GF38Check(conjugated = ctxB.group,
                     "MeatAxe conjugating matrix failed direct matrix-group equality");
            return rec(isConjugate := true,
                       conjugatingMatrixAtoB := X,
                       outerCosetsTested := tested,
                       outerCosetsTotal := Length(ctxA.outerTransversal));
        fi;
    od;
    return rec(isConjugate := false,
               outerCosetsTested := tested,
               outerCosetsTotal := Length(ctxA.outerTransversal));
end;;

# Exact conjugacy through the characteristic O_2 core.
# The restricted modules are checked to be homogeneous.  Once two copies of
# the core have been aligned, every conjugating matrix lies in its full linear
# normaliser.  This normaliser is constructed from the full automorphism group
# of the core and MeatAxe intertwiners.  Invariants are not used as conjugacy
# decisions.

GF38TwoCoreContext := function(G, p)
    local fullIso, fullPc, corePcInFull, core, coreIso, corePc, corePcgens,
          coreGens, module, collected, centreOrder, derivedOrder,
          frattiniOrder;
    fullIso := IsomorphismPcGroup(G);
    fullPc := Image(fullIso);
    corePcInFull := PCore(fullPc, 2);
    core := Group(List(GeneratorsOfGroup(corePcInFull),
                       x -> PreImagesRepresentative(fullIso, x)));
    GF38Check(IsNormal(G, core),
             "computed O_2 is not normal in its full matrix group");
    GF38Check(Size(core) > 1 and IsPGroup(core) and PrimePGroup(core) = 2,
             "computed O_2 is not a nontrivial 2-group");
    coreIso := IsomorphismPcGroup(core);
    corePc := Image(coreIso);
    corePcgens := GeneratorsOfGroup(corePc);
    coreGens := List(corePcgens,
                     x -> PreImagesRepresentative(coreIso, x));
    module := GModuleByMats(coreGens, GF(p));
    collected := MTX.CollectedFactors(module);
    GF38Check(Length(collected) = 1,
             "the characteristic O_2 module is not homogeneous");
    GF38Check(MTX.IsIrreducible(collected[1][1]),
             "the representative O_2 constituent is not irreducible");
    GF38Check(MTX.Dimension(collected[1][1]) * collected[1][2] =
             MTX.Dimension(module),
             "O_2 homogeneous multiplicity does not recover the module dimension");
    centreOrder := Size(Centre(corePc));
    derivedOrder := Size(DerivedSubgroup(corePc));
    frattiniOrder := Size(FrattiniSubgroup(corePc));
    return rec(fullGroup := G,
               core := core,
               coreOrder := Size(core),
               iso := coreIso,
               pc := corePc,
               pcgens := corePcgens,
               coreGenerators := coreGens,
               module := module,
               moduleIsIrreducible := MTX.IsIrreducible(module),
               endomorphismDimension :=
                   Length(SMTX.BasisModuleEndomorphisms(module)),
               constituentDimension := MTX.Dimension(collected[1][1]),
               homogeneousMultiplicity := collected[1][2],
               structure := rec(order := Size(corePc),
                   centreOrder := centreOrder,
                   derivedOrder := derivedOrder,
                   frattiniOrder := frattiniOrder,
                   exponent := Exponent(corePc),
                   smallGroupId := IdGroup(corePc),
                   isExtraspecial := centreOrder = 2 and
                       derivedOrder = 2 and frattiniOrder = 2));
end;;

# Retain the characteristic O_2 data of each matrix group.  A group can enter
# several exact comparisons, but its pc image, O_2 and restricted module do
# not change between them.
if not IsBound(GF38KnownTwoCoreContexts) then
    GF38KnownTwoCoreContexts := [];
fi;

GF38GetTwoCoreContext := function(G, p)
    local known, context;
    for known in GF38KnownTwoCoreContexts do
        if known.p = p and IsIdenticalObj(known.group, G) then
            return known.context;
        fi;
    od;
    context := GF38TwoCoreContext(G, p);
    Add(GF38KnownTwoCoreContexts,
        rec(p := p, group := G, context := context));
    return context;
end;;

GF38CoreClassPolynomial := function(ctx, element)
    return CoefficientsOfUnivariatePolynomial(
        CharacteristicPolynomial(PreImagesRepresentative(ctx.iso, element)));
end;;

# Build the exact action of Aut(O_2) on conjugacy classes.  Because 3 does
# not divide |O_2|, the restricted module is semisimple.  Brauer--Nesbitt
# therefore makes its characteristic polynomial on every O_2 class a
# complete module-isomorphism invariant, not merely a filter.
GF38PrepareCoreClassAction := function(ctx)
    local classes, representatives, automorphisms, automorphismGenerators,
          permutationImages, alpha, imagePositions, x, position,
          permutationGroup, actionHomomorphism;
    if IsBound(ctx.classActionReady) and ctx.classActionReady then
        return;
    fi;
    classes := ConjugacyClasses(ctx.pc);
    representatives := List(classes, Representative);
    automorphisms := AutomorphismGroup(ctx.pc);
    automorphismGenerators := GeneratorsOfGroup(automorphisms);
    permutationImages := [];
    for alpha in automorphismGenerators do
        imagePositions := [];
        for x in representatives do
            position := PositionProperty(classes, c -> Image(alpha, x) in c);
            GF38Check(position <> fail,
                     "an O_2 automorphism did not permute its classes");
            Add(imagePositions, position);
        od;
        Add(permutationImages, PermList(imagePositions));
    od;
    permutationGroup := Group(permutationImages);
    actionHomomorphism := GroupHomomorphismByImages(
        automorphisms, permutationGroup, automorphismGenerators,
        permutationImages);
    GF38Check(actionHomomorphism <> fail,
             "failed to construct the O_2 class-action homomorphism");
    ctx.coreClasses := classes;
    ctx.coreClassRepresentatives := representatives;
    ctx.automorphisms := automorphisms;
    ctx.classPermutationGroup := permutationGroup;
    ctx.classActionHomomorphism := actionHomomorphism;
    ctx.moduleClassInvariant :=
        List(representatives, x -> GF38CoreClassPolynomial(ctx, x));
    ctx.classActionReady := true;
end;;

# Return a record whose matrix X satisfies X^-1*ctxA.core*X=ctxB.core.
# Failure of the exact Aut(O_2)-orbit test is a sound negative conclusion.
GF38AlignTwoCores := function(ctxA, ctxB, p)
    local phi, targetInvariant, permutationRepresentative,
          permutationCandidates, permutationImage, alpha, imgs,
          imageModule, X, i, conjugated;
    if ctxA.coreOrder <> ctxB.coreOrder then
        return rec(isAligned := false, exactNegative := true,
                   reason := "different-core-orders");
    fi;
    if ctxA.core = ctxB.core then
        return rec(isAligned := true,
                   matrix := IdentityMat(MTX.Dimension(ctxA.module), GF(p)),
                   reason := "identical-matrix-cores");
    fi;
    if ctxA.structure.smallGroupId <> ctxB.structure.smallGroupId then
        return rec(isAligned := false, exactNegative := true,
                   reason := "nonisomorphic-core-types");
    fi;
    phi := IsomorphismGroups(ctxA.pc, ctxB.pc);
    GF38Check(phi <> fail,
             "equal O_2 SmallGroups identifiers lacked an isomorphism");
    GF38PrepareCoreClassAction(ctxA);
    targetInvariant := List(ctxA.coreClassRepresentatives, x ->
        GF38CoreClassPolynomial(ctxB, Image(phi, x)));
    permutationRepresentative := RepresentativeAction(
        ctxA.classPermutationGroup, targetInvariant,
        ctxA.moduleClassInvariant, Permuted);
    if permutationRepresentative = fail then
        return rec(isAligned := false, exactNegative := true,
                   reason := "distinct-core-module-orbits");
    fi;
    permutationCandidates := Set(
        [permutationRepresentative, permutationRepresentative^-1]);
    for permutationImage in permutationCandidates do
        alpha := PreImagesRepresentative(ctxA.classActionHomomorphism,
                                          permutationImage);
        imgs := List(ctxA.pcgens, x ->
            PreImagesRepresentative(ctxB.iso,
                Image(phi, Image(alpha, x))));
        imageModule := GModuleByMats(imgs, GF(p));
        X := MTX.IsomorphismModules(ctxA.module, imageModule);
        if X <> fail then
            GF38Check(Length(X) = Length(X[1]) and RankMat(X) = Length(X),
                     "core alignment returned a non-invertible matrix");
            for i in [1 .. Length(ctxA.coreGenerators)] do
                GF38Check(X^-1 * ctxA.coreGenerators[i] * X = imgs[i],
                         "core alignment failed a generator check");
            od;
            conjugated := Group(List(GeneratorsOfGroup(ctxA.core),
                                      g -> X^-1 * g * X));
            GF38Check(conjugated = ctxB.core,
                     "core alignment failed direct matrix-group equality");
            return rec(isAligned := true, matrix := X,
                       reason := "class-orbit-and-meataxe");
        fi;
    od;
    GF38Stop("Brauer--Nesbitt class orbit did not yield a MeatAxe alignment");
end;;

# GAP constructs the full ambient linear normaliser directly.  The
# independently computed MeatAxe module-automorphism group must equal its
# direct GL-centraliser; this checks the kernel also for multiplicity b>1.
GF38BuildTwoCoreNormaliser := function(coreCtx, p)
    local gl, N, centraliser, moduleAutomorphisms, quotientMap, quotient;
    gl := GL(MTX.Dimension(coreCtx.module), p);
    N := Normalizer(gl, coreCtx.core);
    centraliser := Centralizer(gl, coreCtx.core);
    moduleAutomorphisms := MTX.ModuleAutomorphisms(coreCtx.module);
    GF38Check(moduleAutomorphisms = centraliser,
             "MeatAxe and direct GL centralisers of O_2 disagree");
    GF38Check(IsNormal(N, coreCtx.core) and
             IsSubgroup(N, centraliser),
             "direct GL normaliser/centraliser containment failed");
    quotientMap := NaturalHomomorphismByNormalSubgroup(N, coreCtx.core);
    quotient := Image(quotientMap);
    GF38Check(Size(quotient) * coreCtx.coreOrder = Size(N),
             "N/O_2 order does not recover the full normaliser order");
    return rec(group := N,
               order := Size(N),
               core := coreCtx.core,
               coreOrder := coreCtx.coreOrder,
               centraliserOrder := Size(centraliser),
               automorphismImageOrder := Size(N) / Size(centraliser),
               quotientMap := quotientMap,
               quotient := quotient,
               quotientOrder := Size(quotient),
               moduleIsIrreducible := coreCtx.moduleIsIrreducible,
               endomorphismDimension := coreCtx.endomorphismDimension,
               constituentDimension := coreCtx.constituentDimension,
               homogeneousMultiplicity := coreCtx.homogeneousMultiplicity,
               structure := coreCtx.structure);
end;;

if not IsBound(GF38KnownNormalisers) then
    GF38KnownNormalisers := [];
fi;

GF38GetTwoCoreNormaliser := function(coreCtx, p)
    local known, built;
    for known in GF38KnownNormalisers do
        if known.p = p and known.core = coreCtx.core then
            return known.normaliser;
        fi;
    od;
    built := GF38BuildTwoCoreNormaliser(coreCtx, p);
    Add(GF38KnownNormalisers,
        rec(p := p, core := coreCtx.core, normaliser := built));
    return built;
end;;

# Exact GL(d,p)-conjugacy using the characteristic subgroup O_2.  If the
# returned record has isConjugate=true, its field conjugatingMatrixAtoB is a
# matrix W satisfying W^-1 A W=B.
GF38ExactConjugacyViaTwoCore := function(groupA, groupB, p)
    local ctxA, ctxB, alignment, alignedA, normaliser, imageA, imageB,
          quotientRepresentative, representative, conjugatingMatrix, conjugated,
          common;
    if Size(groupA) <> Size(groupB) then
        return rec(isConclusive := true, isConjugate := false,
                   stage := "order");
    fi;
    ctxA := GF38GetTwoCoreContext(groupA, p);
    ctxB := GF38GetTwoCoreContext(groupB, p);
    # For multiplicity four, constructing the quotient action of the full
    # normaliser of O_2 is slower than the independent exhaustive
    # automorphism-and-intertwiner calculation.  In this case no negative
    # conclusion is drawn here; GF38ExactConjugacyByAutomorphisms performs the
    # exact comparison instead.
    if ctxA.homogeneousMultiplicity > 2 or
       ctxB.homogeneousMultiplicity > 2 then
        return rec(isConclusive := false,
                   stage := "high-homogeneous-multiplicity",
                   coreOrderA := ctxA.coreOrder,
                   coreOrderB := ctxB.coreOrder,
                   coreStructureA := ctxA.structure,
                   coreStructureB := ctxB.structure,
                   homogeneousMultiplicityA :=
                       ctxA.homogeneousMultiplicity,
                   homogeneousMultiplicityB :=
                       ctxB.homogeneousMultiplicity,
                   constituentDimensionA := ctxA.constituentDimension,
                   constituentDimensionB := ctxB.constituentDimension,
                   coreEndomorphismDimensionA :=
                       ctxA.endomorphismDimension,
                   coreEndomorphismDimensionB :=
                       ctxB.endomorphismDimension);
    fi;
    alignment := GF38AlignTwoCores(ctxA, ctxB, p);
    if not alignment.isAligned then
        GF38Check(alignment.exactNegative,
                 "inconclusive core alignment was treated as negative");
        return rec(isConclusive := true, isConjugate := false,
                   stage := alignment.reason,
                   coreOrderA := ctxA.coreOrder,
                   coreOrderB := ctxB.coreOrder,
                   coreStructureA := ctxA.structure,
                   coreStructureB := ctxB.structure,
                   quotientConjugacyResult := false);
    fi;
    alignedA := Group(List(GeneratorsOfGroup(groupA),
                            g -> alignment.matrix^-1 * g * alignment.matrix));
    normaliser := GF38GetTwoCoreNormaliser(ctxB, p);
    GF38Check(IsSubgroup(normaliser.group, alignedA),
             "core-aligned first group is not in the computed normaliser");
    GF38Check(IsSubgroup(normaliser.group, groupB),
             "second group is not in the computed normaliser of its characteristic 2-subgroup");
    imageA := Image(normaliser.quotientMap, alignedA);
    imageB := Image(normaliser.quotientMap, groupB);
    quotientRepresentative := RepresentativeAction(normaliser.quotient,
                                                     imageA, imageB, OnPoints);
    if quotientRepresentative = fail then
        return rec(isConclusive := true, isConjugate := false,
                   stage := "normaliser-quotient",
                   coreOrder := ctxB.coreOrder,
                   coreStructure := normaliser.structure,
                   homogeneousMultiplicity :=
                       normaliser.homogeneousMultiplicity,
                   constituentDimension := normaliser.constituentDimension,
                   coreEndomorphismDimension :=
                       normaliser.endomorphismDimension,
                   coreCentraliserOrder := normaliser.centraliserOrder,
                   normaliserOrder := normaliser.order,
                   quotientOrder := normaliser.quotientOrder,
                   quotientConjugacyResult := false);
    fi;
    representative := PreImagesRepresentative(normaliser.quotientMap,
                                               quotientRepresentative);
    conjugatingMatrix := alignment.matrix * representative;
    conjugated := Group(List(GeneratorsOfGroup(groupA),
                              g -> conjugatingMatrix^-1 * g * conjugatingMatrix));
    GF38Check(conjugated = groupB,
              "O_2-normaliser conjugating matrix failed direct matrix-group equality");
    return rec(isConclusive := true, isConjugate := true,
               conjugatingMatrixAtoB := conjugatingMatrix,
               stage := "verified",
               coreOrder := ctxB.coreOrder,
               coreStructure := normaliser.structure,
               homogeneousMultiplicity :=
                   normaliser.homogeneousMultiplicity,
               constituentDimension := normaliser.constituentDimension,
               normaliserOrder := normaliser.order,
               normaliserAutomorphismImageOrder :=
                   normaliser.automorphismImageOrder,
               coreCentraliserOrder := normaliser.centraliserOrder,
               coreModuleIsIrreducible := normaliser.moduleIsIrreducible,
               coreEndomorphismDimension :=
                   normaliser.endomorphismDimension,
               quotientOrder := normaliser.quotientOrder,
               quotientConjugacyResult := true);
end;;

# Structural checks for the stored comparison groups and the enumerated groups.
# The checks below are repeated for every group used in an exact comparison.
CheckReferenceData := function(referenceData)
    local names, counts, pos, i, j, r, data, expectedRowLabels;
    GF38Check(IsRecord(referenceData), "reference data is not a record");
    GF38Check(IsBound(referenceData.p) and referenceData.p = 3 and
             IsBound(referenceData.d) and referenceData.d = 8,
             "reference data field/dimension header is not GF(3)^8");
    GF38Check(IsBound(referenceData.holtYangCount) and referenceData.holtYangCount = 189,
             "reference data Holt--Yang record count is not 189");
    GF38Check(IsBound(referenceData.surplusCount) and referenceData.surplusCount = 12,
             "reference data surplus count is not 12");
    GF38Check(IsBound(referenceData.totalReferenceCount) and
             referenceData.totalReferenceCount = 201,
             "reference data total reference count is not 201");
    GF38Check(IsBound(referenceData.references) and Length(referenceData.references) = 201,
             "reference data reference list does not have 201 records");
    names := [ "Line9gpsp", "Line9gpsm", "Line22gps",
               "Line75gps", "Line117gps" ];
    counts := [27, 71, 72, 10, 9];
    GF38Check(referenceData.referenceFileNames = names and
             referenceData.referenceFileCounts = counts,
             "reference data reference file names/counts or their order changed");
    pos := 1;
    for i in [1 .. Length(names)] do
        for j in [1 .. counts[i]] do
            r := referenceData.references[pos];
            GF38Check(r.index = pos and r.kind = "holtYang" and
                     r.file = names[i] and r.fileIndex = j,
                     Concatenation("reference ordering mismatch at index ",
                                   String(pos)));
            GF38Check(IsBound(r.classInvariant) and r.classInvariant[1] = r.order,
                     Concatenation("reference order/invariant mismatch at ",
                                   String(pos)));
            pos := pos + 1;
        od;
    od;
    for j in [1 .. 12] do
        r := referenceData.references[pos];
        GF38Check(r.index = pos and r.kind = "surplus" and
                 r.file = "SurplusGroups" and r.fileIndex = j,
                 Concatenation("surplus ordering mismatch at index ",
                               String(pos)));
        GF38Check(r.classInvariant[1] = r.order,
                 Concatenation("surplus order/invariant mismatch at ",
                               String(pos)));
        pos := pos + 1;
    od;
    GF38Check(pos = 202, "the 201 comparison records were not all checked");

    GF38Check(IsBound(referenceData.datasets.remainingRows) and
             IsBound(referenceData.datasets.row117) and
             IsBound(referenceData.datasets.rows110And113),
             "reference data is missing a comparison set");
    data := referenceData.datasets.remainingRows;
    GF38Check(data.name = "remainingRows" and data.count = 152 and
             Length(data.records) = 152,
             "remaining-rows reference data header/count is wrong");
    expectedRowLabels := [ "9 (E+)", "9 (E-)", "75",
                           "117 (E+)", "117 (E-)" ];
    GF38Check(data.rowLabels = expectedRowLabels,
             "remaining-row label order changed");
    for i in [1 .. 152] do
        r := data.records[i];
        GF38Check(r.index = i and r.classInvariant[1] = r.order,
                 Concatenation("remaining-rows ordering mismatch at item ",
                               String(i)));
        GF38Check(IsList(r.rowLabels) and Length(r.rowLabels) > 0 and
                  ForAll(r.rowLabels, label -> label in expectedRowLabels),
                 Concatenation("remaining-row labels invalid at item ",
                               String(i)));
    od;

    data := referenceData.datasets.row117;
    GF38Check(data.name = "row117" and data.count = 118 and
             Length(data.records) = 118,
             "row-117 reference data header/count is wrong");
    for i in [1 .. 118] do
        r := data.records[i];
        GF38Check(r.index = i and r.classInvariant[1] = r.order,
                 Concatenation("row-117 reference ordering mismatch at item ",
                               String(i)));
    od;

    data := referenceData.datasets.rows110And113;
    GF38Check(data.name = "rows110And113" and data.count = 88 and
             Length(data.records) = 88,
             "rows-110-and-113 reference data header/count is wrong");
    for i in [1 .. 88] do
        r := data.records[i];
        GF38Check(r.index = i and r.classInvariant[1] = r.order,
                 Concatenation("rows-110-and-113 ordering mismatch at item ",
                               String(i)));
    od;
end;;
