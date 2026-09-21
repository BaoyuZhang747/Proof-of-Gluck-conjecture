# Complete enumeration of the Holt--Yang rows on GF(3)^8.

# The rows are 9+, 9-, 22, 75, 110, 113+, 113-, 117+ and 117-.
# Each calculation starts from the normal subgroup prescribed by the row.
# Subgroups of its normaliser quotient are lifted and tested for the five defining
# properties.  Rows 75 and 113 require more than one normaliser quotient; the
# reason for each decomposition is explained where it is used below.

# Equality of characteristic-polynomial data is used only to locate possible
# conjugates.  Every equality of GL(8,3)-classes is decided either in the full
# normaliser of the characteristic 2-core or by the exhaustive automorphism and
# module-intertwining test in gf3_8_conjugacy_methods.g.

if LoadPackage("irredsol") <> true then
    Error("the GAP package IrredSol is required");
fi;

Read("matrix_group_tests.g");;
Read("gf3_8_conjugacy_methods.g");;
Read("gf3_8_constructions.g");;

GF38NewClassList := function()
    return rec(groups := [], invariants := [], contexts := [], rowLabels := []);
end;;

# Form the polycyclic (pc) representation and the characteristic-polynomial data of a
# matrix group once.  The same group often occurs in more than one of the
# unions compared below.
GF38KnownGroupData := [];;
GF38GroupData := function(group)
    local known, context, data;
    for known in GF38KnownGroupData do
        if IsIdenticalObj(known.group, group) then
            return known.data;
        fi;
    od;
    context := GF38ExactContext(group);
    data := rec(invariant :=
                    [context.order,
                     SortedList(List(ConjugacyClasses(context.pc), class ->
                         [Size(class),
                          CoefficientsOfUnivariatePolynomial(
                              CharacteristicPolynomial(
                                  PreImagesRepresentative(
                                      context.iso,
                                      Representative(class))))]))],
                context := context);
    Add(GF38KnownGroupData, rec(group := group, data := data));
    return data;
end;;

GF38ExactEquality := function(firstGroup, firstContext,
                              secondGroup, secondContext)
    local known, result, isConjugate;
    if IsIdenticalObj(firstGroup, secondGroup) then
        return true;
    fi;
    for known in firstContext.comparisonResults do
        if IsIdenticalObj(known.group, secondGroup) then
            return known.isConjugate;
        fi;
    od;
    # The two-core calculation constructs the normaliser of its second
    # argument.  The first group here is the retained class representative, so
    # put it second and reuse its normaliser in later comparisons.
    result := GF38ExactConjugacyViaTwoCore(secondGroup, firstGroup, 3);
    if result.isConclusive then
        isConjugate := result.isConjugate;
    else
        # In the automorphism calculation the first context is the expensive
        # one to prepare.  Keep the retained class representative first.
        result := GF38ExactConjugacyByAutomorphisms(firstContext,
                                                    secondContext, 3);
        isConjugate := result.isConjugate;
    fi;
    Add(firstContext.comparisonResults,
        rec(group := secondGroup, isConjugate := isConjugate));
    Add(secondContext.comparisonResults,
        rec(group := firstGroup, isConjugate := isConjugate));
    return isConjugate;
end;;

# Insert a group unless it is GL(8,3)-conjugate to an earlier member.  Row
# labels are retained because one class can arise from several rows.
GF38InsertClass := function(classes, group, rowLabel)
    local data, invariant, context, i;
    data := GF38GroupData(group);
    invariant := data.invariant;
    context := data.context;
    for i in [1 .. Length(classes.groups)] do
        if classes.invariants[i] = invariant and
           GF38ExactEquality(classes.groups[i], classes.contexts[i],
                             group, context) then
            if rowLabel <> fail then
                AddSet(classes.rowLabels[i], rowLabel);
            fi;
            return i;
        fi;
    od;
    Add(classes.groups, group);
    Add(classes.invariants, invariant);
    Add(classes.contexts, context);
    if rowLabel = fail then
        Add(classes.rowLabels, []);
    else
        Add(classes.rowLabels, [rowLabel]);
    fi;
    return Length(classes.groups);
end;;

GF38InsertGroups := function(classes, groups, rowLabel)
    local group;
    for group in groups do
        GF38InsertClass(classes, group, rowLabel);
    od;
end;;

GF38ClassPosition := function(classes, group)
    local data, invariant, context, i;
    data := GF38GroupData(group);
    invariant := data.invariant;
    context := data.context;
    for i in [1 .. Length(classes.groups)] do
        if classes.invariants[i] = invariant and
           GF38ExactEquality(classes.groups[i], classes.contexts[i],
                             group, context) then
            return i;
        fi;
    od;
    return fail;
end;;

GF38CheckCoreAndNormaliser := function(label, data, coreOrder, centreOrder,
                                       normaliserOrder)
    GF38AssertEqual(Concatenation(label, ": order of the prescribed subgroup"),
                    Size(data.core), coreOrder);
    GF38AssertEqual(Concatenation(label, ": centre order"),
                    Size(Centre(data.core)), centreOrder);
    GF38AssertEqual(Concatenation(label, ": ambient-group order"),
                    Size(data.normaliser), normaliserOrder);
    if not IsNormal(data.normaliser, data.core) then
        Error(label, ": the prescribed subgroup is not normal in its stated ambient group");
    fi;
end;;

GF38CheckQuotientResult := function(label, result, quotientOrder,
                                    subgroupClasses, solvableClasses,
                                    qualifyingGroups)
    GF38AssertEqual(Concatenation(label, ": quotient order"),
                    result.quotientOrder, quotientOrder);
    GF38AssertEqual(Concatenation(label, ": subgroup classes"),
                    result.subgroupClassCount, subgroupClasses);
    if solvableClasses <> fail then
        GF38AssertEqual(Concatenation(label, ": solvable subgroup classes"),
                        result.solvableClassCount, solvableClasses);
    fi;
    GF38AssertEqual(Concatenation(label, ": qualifying groups"),
                    Length(result.accepted), qualifyingGroups);
end;;

# The five Holt--Yang files contain 189 records.  They are comparison data only:
# none of them is used to construct a normaliser or to decide whether a lifted
# subgroup satisfies the five properties.
GF38ReferenceFileNames := ["Line9gpsp", "Line9gpsm", "Line22gps",
                           "Line75gps", "Line117gps"];;
GF38ReferenceFileCounts := [27, 71, 72, 10, 9];;
GF38References := [];;
GF38HoltYangGroups := [];;
GF38ReferenceIndex := 0;;

for GF38FileNumber in [1 .. Length(GF38ReferenceFileNames)] do
    GF38FileName := GF38ReferenceFileNames[GF38FileNumber];
    GF38Path := Concatenation("holt_yang_data/", GF38FileName, ".g");
    if not IsReadableFile(GF38Path) then
        Error("the Holt--Yang group file is missing: ", GF38Path);
    fi;
    Read(GF38Path);
    if not IsBoundGlobal(GF38FileName) then
        Error(GF38Path, " did not define ", GF38FileName);
    fi;
    GF38FileGroups := ValueGlobal(GF38FileName);
    GF38AssertEqual(Concatenation(GF38FileName, ": number of records"),
                    Length(GF38FileGroups),
                    GF38ReferenceFileCounts[GF38FileNumber]);
    for GF38FileIndex in [1 .. Length(GF38FileGroups)] do
        GF38Group := GF38FileGroups[GF38FileIndex];
        GF38ReferenceIndex := GF38ReferenceIndex + 1;
        Add(GF38HoltYangGroups, GF38Group);
        Add(GF38References,
            rec(index := GF38ReferenceIndex,
                kind := "holtYang",
                file := GF38FileName,
                fileIndex := GF38FileIndex,
                order := Size(GF38Group),
                generators := GeneratorsOfGroup(GF38Group),
                classInvariant := GF38GroupData(GF38Group).invariant));
    od;
od;
GF38AssertEqual("Holt--Yang records on GF(3)^8",
                Length(GF38HoltYangGroups), 189);

# These twelve stored groups order the omitted classes.  Exact conjugacy
# comparisons below match them with representatives obtained from the row-22
# enumeration.
Read("gf3_8_additional_groups.g");;
if not IsBound(GF38AdditionalGroups) then
    Error("gf3_8_additional_groups.g did not define GF38AdditionalGroups");
fi;
GF38AssertEqual("stored groups for the twelve omitted classes",
                Length(GF38AdditionalGroups), 12);
GF38SurplusGroups := List(GF38AdditionalGroups,
                          entry -> Group(entry.generators));;
for GF38FileIndex in [1 .. 12] do
    GF38Group := GF38SurplusGroups[GF38FileIndex];
    GF38ReferenceIndex := GF38ReferenceIndex + 1;
    Add(GF38References,
        rec(index := GF38ReferenceIndex,
            kind := "surplus",
            file := "SurplusGroups",
            fileIndex := GF38FileIndex,
            order := Size(GF38Group),
            generators := GF38AdditionalGroups[GF38FileIndex].generators,
            classInvariant := GF38GroupData(GF38Group).invariant));
od;
GF38AssertEqual("Holt--Yang and omitted reference records",
                Length(GF38References), 201);

GF38HoltYangClasses := GF38NewClassList();;
GF38HoltYangClassPositions := List(GF38HoltYangGroups,
    group -> GF38InsertClass(GF38HoltYangClasses, group, fail));;
GF38AssertEqual("GL(8,3)-classes represented by the 189 Holt--Yang records",
                Length(GF38HoltYangClasses.groups), 140);

GF38HoltYangIncidences := List(
    [1 .. Length(GF38HoltYangClasses.groups)],
    classPosition -> Filtered(
        [1 .. Length(GF38HoltYangClassPositions)],
        referencePosition ->
            GF38HoltYangClassPositions[referencePosition] = classPosition));;
GF38HoltYangFileSets := List(GF38HoltYangIncidences,
    incidence -> Set(List(incidence,
        referencePosition -> GF38References[referencePosition].file)));;
GF38AssertEqual("absence of repetitions within a Holt--Yang file",
    ForAll([1 .. Length(GF38HoltYangIncidences)], classPosition ->
        Length(GF38HoltYangIncidences[classPosition]) =
        Length(GF38HoltYangFileSets[classPosition])), true);
GF38AssertEqual("classes occurring in all three row-9 and row-22 files",
    Number(GF38HoltYangFileSets, files ->
        files = Set(["Line9gpsp", "Line9gpsm", "Line22gps"])), 9);
GF38AssertEqual("classes occurring in row 22 and exactly one row-9 file",
    Number(GF38HoltYangFileSets, files ->
        Length(files) = 2 and "Line22gps" in files and
        ("Line9gpsp" in files or "Line9gpsm" in files)), 27);
GF38AssertEqual("classes occurring in the row-22 and row-117 files",
    Number(GF38HoltYangFileSets, files ->
        files = Set(["Line22gps", "Line117gps"])), 4);
GF38AssertEqual("classes represented in more than one Holt--Yang file",
    Number(GF38HoltYangIncidences,
           incidence -> Length(incidence) > 1), 40);

GF38Row22Row117Pairs := [];;
for GF38FirstReference in [1 .. Length(GF38HoltYangClassPositions)] do
    if GF38References[GF38FirstReference].file = "Line22gps" then
        for GF38SecondReference in
            [1 .. Length(GF38HoltYangClassPositions)] do
            if GF38References[GF38SecondReference].file = "Line117gps" and
               GF38HoltYangClassPositions[GF38FirstReference] =
               GF38HoltYangClassPositions[GF38SecondReference] then
                Add(GF38Row22Row117Pairs,
                    [GF38References[GF38FirstReference].fileIndex,
                     GF38References[GF38SecondReference].fileIndex]);
            fi;
        od;
    fi;
od;
GF38AssertEqual("row-22 and row-117 record identifications",
    GF38Row22Row117Pairs,
    [[13, 3], [14, 1], [15, 2], [21, 9]]);

GF38Line75SingletonIndices := List(
    Filtered([1 .. Length(GF38HoltYangClassPositions)],
        referencePosition ->
            GF38References[referencePosition].file = "Line75gps" and
            Length(GF38HoltYangIncidences[
                GF38HoltYangClassPositions[referencePosition]]) = 1),
    referencePosition -> GF38References[referencePosition].fileIndex);;
GF38AssertEqual("row-75 records represented in no other file",
    GF38Line75SingletonIndices, [1 .. 10]);

GF38SurplusClasses := GF38NewClassList();;
GF38InsertGroups(GF38SurplusClasses, GF38SurplusGroups, fail);
GF38AssertEqual("GL(8,3)-classes among the twelve omitted groups",
                Length(GF38SurplusClasses.groups), 12);
GF38AssertEqual("orders of the twelve omitted classes",
    Collected(SortedList(List(GF38SurplusClasses.groups, Size))),
    [[1152, 1], [2304, 11]]);
GF38SurplusTwoCoreData := List(GF38SurplusGroups,
    group -> GF38GetTwoCoreContext(group, 3));;
if not ForAll(GF38SurplusTwoCoreData, context -> context.coreOrder = 64) then
    Error("a stored representative of an omitted class does not have O_2 of order 64");
fi;
for GF38Group in GF38SurplusGroups do
    if GF38ClassPosition(GF38HoltYangClasses, GF38Group) <> fail then
        Error("a stated omitted class is conjugate to a Holt--Yang group");
    fi;
od;

GF38ReferenceClasses := GF38NewClassList();;
GF38InsertGroups(GF38ReferenceClasses,
                 Concatenation(GF38HoltYangGroups, GF38SurplusGroups), fail);
GF38AssertEqual("classes represented by the 201 reference records",
                Length(GF38ReferenceClasses.groups), 152);
Print("The 189 Holt--Yang records represent 140 classes; together with the ",
      "twelve omitted classes they give 152 classes.\n");

# Rows 9+ and 9-.
GF38Row9PlusData := GF38CoreAndNormaliser("E+", 8, 1, 1);;
GF38CheckCoreAndNormaliser("row 9+", GF38Row9PlusData, 128, 2, 5160960);
GF38Row9Plus := GF38EnumerateQuotient(GF38Row9PlusData.core,
                                      GF38Row9PlusData.normaliser, "row 9+");;
GF38CheckQuotientResult("row 9+", GF38Row9Plus, 40320, 296, 268, 27);

GF38Row9MinusData := GF38CoreAndNormaliser("E-", 8, 1, 1);;
GF38CheckCoreAndNormaliser("row 9-", GF38Row9MinusData, 128, 2, 6635520);
GF38Row9Minus := GF38EnumerateQuotient(GF38Row9MinusData.core,
                                       GF38Row9MinusData.normaliser, "row 9-");;
GF38CheckQuotientResult("row 9-", GF38Row9Minus, 51840, 350, 331, 71);

# Row 22.  This is a direct enumeration of all 914 subgroup classes of N/S;
# the twelve omitted classes are not imported into the calculation.
GF38Row22Data := GF38CoreAndNormaliser("S", 4, 2, 1);;
GF38CheckCoreAndNormaliser("row 22", GF38Row22Data, 64, 4, 184320);
GF38Row22IntrinsicCore := Group(Filtered(
    Elements(GF38Row22Data.localTwoCore),
    element -> element^4 = One(GF38Row22Data.localTwoCore)));;
GF38AssertEqual("row 22 intrinsic symplectic-type subgroup",
    GF38Row22IntrinsicCore, GF38Row22Data.coreOverExtension);
GF38Row22NormaliserCheck := GF38VerifySemilinearNormaliser(
    "row 22", GF38Row22Data, GF38Row22Data.core,
    GF38Row22Data.localNormaliser, 2, 92160, 184320);;
GF38AssertEqual("row 22 symplectic-type subgroup order",
                Size(GF38Row22NormaliserCheck.core), 64);
GF38AssertEqual("row 22 ambient-group 2-core order",
                Size(PCore(GF38Row22Data.normaliser, 2)), 256);
GF38Row22 := GF38EnumerateQuotient(GF38Row22Data.core,
                                   GF38Row22Data.normaliser, "row 22");;
GF38CheckQuotientResult("row 22", GF38Row22, 2880, 914, 866, 80);
GF38Row22Classes := GF38NewClassList();;
GF38InsertGroups(GF38Row22Classes, GF38Row22.accepted, "22");
GF38AssertEqual("distinct classes produced by row 22",
                Length(GF38Row22Classes.groups), 80);

GF38Row22HoltYang := 0;;
GF38Row22Surplus := 0;;
GF38MatchedSurplus := [];;
GF38EnumeratedSurplusGroups := List([1 .. 12], i -> fail);;
GF38MatchedHoltYangClassPositions := [];;
for GF38Group in GF38Row22Classes.groups do
    GF38HoltYangPosition := GF38ClassPosition(GF38HoltYangClasses, GF38Group);
    GF38SurplusPosition := GF38ClassPosition(GF38SurplusClasses, GF38Group);
    if GF38HoltYangPosition <> fail and GF38SurplusPosition <> fail then
        Error("a row-22 class both occurs in the Holt--Yang data and is stated to be omitted");
    elif GF38HoltYangPosition <> fail then
        GF38Row22HoltYang := GF38Row22HoltYang + 1;
        AddSet(GF38MatchedHoltYangClassPositions, GF38HoltYangPosition);
    elif GF38SurplusPosition <> fail then
        GF38Context := GF38GetTwoCoreContext(GF38Group, 3);
        GF38AssertEqual("2-core order of an omitted row-22 lift",
                        GF38Context.coreOrder, 64);
        if GF38Context.core <> GF38Row22Data.core then
            Error("an omitted row-22 lift does not have the prescribed 2-core");
        fi;
        if GF38EnumeratedSurplusGroups[GF38SurplusPosition] <> fail then
            Error("two enumerated row-22 classes match the same stored omitted class");
        fi;
        GF38EnumeratedSurplusGroups[GF38SurplusPosition] := GF38Group;
        GF38Row22Surplus := GF38Row22Surplus + 1;
        Add(GF38MatchedSurplus, GF38SurplusPosition);
    else
        Error("a row-22 class is absent from both comparison lists");
    fi;
od;
GF38AssertEqual("Holt--Yang classes recovered in row 22", GF38Row22HoltYang, 68);
GF38AssertEqual("omitted classes recovered in row 22", GF38Row22Surplus, 12);
GF38AssertEqual("one-to-one recovery of the twelve omitted groups",
                Set(GF38MatchedSurplus), [1 .. 12]);
GF38AssertEqual("an enumerated representative for each omitted class",
                ForAll(GF38EnumeratedSurplusGroups, G -> G <> fail), true);
for GF38FileIndex in [1 .. 12] do
    GF38Group := GF38EnumeratedSurplusGroups[GF38FileIndex];
    GF38SurplusReferencePosition := PositionProperty(
        [1 .. Length(GF38References)],
        position -> GF38References[position].kind = "surplus" and
                    GF38References[position].fileIndex = GF38FileIndex);
    if GF38SurplusReferencePosition = fail then
        Error("the reference record for an omitted class is missing");
    fi;
    GF38GroupDatum := GF38GroupData(GF38Group);
    GF38AssertEqual("order of an enumerated omitted-class representative",
        Size(GF38Group),
        GF38References[GF38SurplusReferencePosition].order);
    GF38AssertEqual("invariant of an enumerated omitted-class representative",
        GF38GroupDatum.invariant,
        GF38References[GF38SurplusReferencePosition].classInvariant);
    GF38References[GF38SurplusReferencePosition].generators :=
        GeneratorsOfGroup(GF38Group);
    GF38References[GF38SurplusReferencePosition].order := Size(GF38Group);
    GF38References[GF38SurplusReferencePosition].classInvariant :=
        GF38GroupDatum.invariant;
od;
GF38Line22ReferenceNumbers := Filtered(
    [1 .. Length(GF38HoltYangClassPositions)],
    referencePosition -> GF38References[referencePosition].file = "Line22gps");;
GF38AssertEqual("Line22 records absent from the row-22 calculation",
    List(Filtered(GF38Line22ReferenceNumbers,
        referencePosition ->
            not GF38HoltYangClassPositions[referencePosition] in
                GF38MatchedHoltYangClassPositions),
        referencePosition -> GF38References[referencePosition].fileIndex),
    [13, 14, 15, 21]);
Print("Row 22: 80 classes, of which 68 occur in the Holt--Yang data and twelve are omitted.\n");

# Row 75.  Its prescribed symplectic-type subgroup has four extraspecial
# subgroups of index two,
# in two conjugacy classes under the semilinear ambient group.
GF38Row75Data := GF38CoreAndNormaliser("S", 2, 4, 1);;
GF38CheckCoreAndNormaliser("row 75", GF38Row75Data, 16, 4, 7680);
GF38Row75PrescribedModule := GModuleByMats(
    GeneratorsOfGroup(GF38Row75Data.core), GF(3));;
if MTX.IsIrreducible(GF38Row75PrescribedModule) then
    Error("row 75: the prescribed subgroup is unexpectedly irreducible over GF(3)");
fi;
GF38AssertEqual("endomorphism-algebra dimension of the prescribed row-75 subgroup",
    Length(SMTX.BasisModuleEndomorphisms(GF38Row75PrescribedModule)), 8);
GF38AssertEqual("row 75 local normaliser order",
                GF38Row75Data.localNormaliserOrder, 1920);
GF38Row75NormaliserCheck := GF38VerifySemilinearNormaliser(
    "row 75", GF38Row75Data, GF38Row75Data.restrictedLocalTwoCore,
    GF38Row75Data.localTwoCoreNormaliser, 4, 1920, 7680);;
GF38AssertEqual("row 75 characteristic 2-core order",
                Size(GF38Row75NormaliserCheck.core), 64);
GF38AssertEqual("row 75 characteristic 2-core centre order",
                Size(Centre(GF38Row75NormaliserCheck.core)), 16);
if GF38Row75NormaliserCheck.core <> PCore(GF38Row75Data.normaliser, 2) then
    Error("row 75: the restricted local 2-core is not O_2 of the ambient group");
fi;
GF38Row75 := GF38EnumerateSymplecticCore(GF38Row75Data, "row 75");;
GF38AssertEqual("row 75 extraspecial subgroups", GF38Row75.candidateCount, 4);
GF38AssertEqual("row 75 conjugacy classes of extraspecial subgroups",
                GF38Row75.classCount, 2);
GF38AssertEqual("row 75 extraspecial-subgroup normaliser orders",
                SortedList(GF38Row75.normaliserOrders), [2560, 7680]);
GF38AssertEqual("row 75 quotient orders",
                SortedList(GF38Row75.quotientOrders), [320, 960]);
GF38AssertEqual("row 75 counts for the two extraspecial-subgroup normalisers",
    SortedList(List(GF38Row75.normaliserResults, result ->
        [result.normaliserOrder, result.quotientOrder,
         result.subgroupClassCount, result.solvableClassCount,
         result.qualifyingCount])),
    [[2560, 320, 130, 130, 0],
     [7680, 960, 260, 260, 10]]);
GF38AssertEqual("row 75 subgroup classes",
                GF38Row75.subgroupClassCount, 390);
GF38AssertEqual("row 75 qualifying groups", Length(GF38Row75.accepted), 10);

# Groups which contain the whole symplectic group S are also obtained directly
# from the quotient of the full ambient group by S.  This calculation is included
# separately and its classes are compared exactly with the results from the
# two extraspecial-subgroup normalisers, so neither possible O_2 subgroup is
# assumed away.
GF38Row75Direct := GF38EnumerateQuotient(GF38Row75Data.core,
                                         GF38Row75Data.normaliser,
                                         "row 75, full symplectic-type subgroup");;
GF38CheckQuotientResult("row 75, full symplectic-type subgroup",
    GF38Row75Direct, 480, 184, 184, 8);
GF38Row75Classes := GF38NewClassList();;
GF38InsertGroups(GF38Row75Classes, GF38Row75.accepted, "75");
GF38AssertEqual("classes from the extraspecial-subgroup normalisers of row 75",
                Length(GF38Row75Classes.groups), 10);
GF38Row75BeforeDirect := Length(GF38Row75Classes.groups);;
GF38InsertGroups(GF38Row75Classes, GF38Row75Direct.accepted, "75");
GF38AssertEqual("row-75 classes after adjoining the direct S quotient",
                Length(GF38Row75Classes.groups), 10);
GF38AssertEqual("new row-75 classes from the direct S quotient",
                Length(GF38Row75Classes.groups) - GF38Row75BeforeDirect, 0);

# The ten classes do not all have the same characteristic 2-core.  This exact
# calculation records the four possibilities and checks that the two groups
# with 2-core of order 64 have precisely the subgroup whose full normaliser was
# established above.
GF38Row75TwoCoreData := List(GF38Row75Classes.groups,
    group -> GF38GetTwoCoreContext(group, 3));;
GF38AssertEqual("row 75 characteristic 2-core types",
    Collected(SortedList(List(GF38Row75TwoCoreData, context ->
        [context.coreOrder, context.endomorphismDimension]))),
    [[[8, 16], 2], [[16, 8], 3], [[32, 8], 3], [[64, 4], 2]]);
for GF38Context in GF38Row75TwoCoreData do
    if GF38Context.coreOrder = 64 and
       GF38Context.core <> GF38Row75NormaliserCheck.core then
        Error("a row-75 2-core of order 64 is not the subgroup whose normaliser was verified");
    fi;
od;

GF38Line75Groups := GF38HoltYangGroups{[171 .. 180]};;
GF38Line75TwoCoreData := List(GF38Line75Groups,
    group -> GF38GetTwoCoreContext(group, 3));;
GF38AssertEqual("row 75 Holt--Yang 2-core data",
    List(GF38Line75TwoCoreData, context ->
        [context.coreOrder, context.endomorphismDimension]),
    [[64, 4], [64, 4], [8, 16], [16, 8], [8, 16],
     [32, 8], [16, 8], [16, 8], [32, 8], [32, 8]]);
GF38Line75ClassPositions := List(GF38Line75Groups,
    group -> GF38ClassPosition(GF38Row75Classes, group));;
if fail in GF38Line75ClassPositions then
    Error("a Holt--Yang row-75 class was not found by the row-75 enumeration");
fi;
GF38AssertEqual("one-to-one recovery of the ten Holt--Yang row-75 groups",
                Set(GF38Line75ClassPositions), [1 .. 10]);
Print("Row 75: the direct quotient over S has ",
      Length(GF38Row75Direct.accepted),
      " qualifying lifts, all among the ten classes from the two ",
      "extraspecial-subgroup normalisers.\n");

# Rows 117+ and 117-.  The plus-form calculation gives 123 qualifying lifts,
# which reduce to 108 classes.  The 19 qualifying minus-form lifts reduce to
# 16 classes; six of these also occur in the plus-form calculation.
GF38Row117PlusData := GF38CoreAndNormaliser("E+", 4, 1, 2);;
GF38CheckCoreAndNormaliser("row 117+", GF38Row117PlusData, 32, 2, 55296);
GF38Row117Plus := GF38EnumerateQuotient(GF38Row117PlusData.core,
                                        GF38Row117PlusData.normaliser,
                                        "row 117+");;
GF38CheckQuotientResult("row 117+", GF38Row117Plus, 1728, 770, 770, 123);

GF38Row117MinusData := GF38CoreAndNormaliser("E-", 4, 1, 2);;
GF38CheckCoreAndNormaliser("row 117-", GF38Row117MinusData, 32, 2, 92160);
GF38Row117Minus := GF38EnumerateQuotient(GF38Row117MinusData.core,
                                         GF38Row117MinusData.normaliser,
                                         "row 117-");;
GF38CheckQuotientResult("row 117-", GF38Row117Minus, 2880, 467, 434, 19);

# The first five normaliser calculations produce the 152 classes represented
# by the 201 Holt--Yang and omitted comparison records.  Their union is
# retained separately for the exact comparisons in gf3_8_conjugacy.g.  The
# calculations for rows 110 and 113 below prove that no further class occurs.
GF38RemainingRows := GF38NewClassList();;
GF38InsertGroups(GF38RemainingRows, GF38Row9Plus.accepted, "9 (E+)");
GF38InsertGroups(GF38RemainingRows, GF38Row9Minus.accepted, "9 (E-)");
GF38InsertGroups(GF38RemainingRows, GF38Row75Classes.groups, "75");
GF38InsertGroups(GF38RemainingRows, GF38Row117Plus.accepted, "117 (E+)");
GF38InsertGroups(GF38RemainingRows, GF38Row117Minus.accepted, "117 (E-)");
GF38AssertEqual("classes from rows 9, 75 and 117",
                Length(GF38RemainingRows.groups), 152);

GF38Row117Classes := GF38NewClassList();;
GF38InsertGroups(GF38Row117Classes, GF38Row117Plus.accepted, "117 (E+)");
GF38AssertEqual("classes in the full row-117+ normaliser",
                Length(GF38Row117Classes.groups), 108);
GF38Row117MinusClasses := GF38NewClassList();;
GF38InsertGroups(GF38Row117MinusClasses,
                 GF38Row117Minus.accepted, "117 (E-)");
GF38AssertEqual("classes in the full row-117- normaliser",
                Length(GF38Row117MinusClasses.groups), 16);
GF38InsertGroups(GF38Row117Classes, GF38Row117Minus.accepted, "117 (E-)");
GF38AssertEqual("classes in the union of the row-117+ and row-117- calculations",
                Length(GF38Row117Classes.groups), 118);
GF38AssertEqual("row-117 classes occurring for both forms",
    Length(Filtered(GF38Row117Classes.rowLabels, labels ->
        "117 (E+)" in labels and "117 (E-)" in labels)), 6);
GF38Row117MinusOnlyPositions := Filtered(
    [1 .. Length(GF38Row117Classes.groups)], position ->
        "117 (E-)" in GF38Row117Classes.rowLabels[position] and
        not "117 (E+)" in GF38Row117Classes.rowLabels[position]);;
GF38AssertEqual("row-117- classes not occurring for row 117+",
                Length(GF38Row117MinusOnlyPositions), 10);
for GF38Position in GF38Row117MinusOnlyPositions do
    GF38RemainingPosition := GF38ClassPosition(
        GF38RemainingRows, GF38Row117Classes.groups[GF38Position]);
    if GF38RemainingPosition = fail or
       not ("9 (E+)" in GF38RemainingRows.rowLabels[GF38RemainingPosition] or
            "9 (E-)" in GF38RemainingRows.rowLabels[GF38RemainingPosition]) then
        Error("a row-117- class absent from row 117+ does not occur in row 9");
    fi;
od;

# For row 110 we form the full normaliser of the prescribed order-16
# symplectic-type subgroup and consider all 1,560 subgroup classes of its
# non-solvable quotient.
GF38Row110Core := GF38ReducedCore("S", 2, 2, 2);;
GF38AssertEqual("row 110 symplectic-type subgroup order", Size(GF38Row110Core), 16);
GF38Row110Normaliser := Normalizer(GL(8, 3), GF38Row110Core);;
GF38AssertEqual("row 110 full normaliser order",
                Size(GF38Row110Normaliser), 276480);
GF38Row110 := GF38EnumerateQuotient(GF38Row110Core,
                                    GF38Row110Normaliser, "row 110");;
GF38CheckQuotientResult("row 110", GF38Row110, 17280, 1560, 1474, 41);

# Row 113 is covered by the four maximal irreducible solvable multiplicity
# groups in GL(4,3).  Their quotient class totals are 2,876 and 5,993 for the
# two extraspecial forms.
GF38Row113Plus := GF38EnumerateRow113("E+");;
GF38AssertEqual("row 113+ extraspecial subgroup order", Size(GF38Row113Plus.core), 8);
GF38AssertEqual("row 113+ local normaliser order",
                GF38Row113Plus.localNormaliserOrder, 16);
GF38AssertEqual("row 113+ endomorphism-algebra dimension",
                GF38Row113Plus.endomorphismAlgebraDimension, 16);
GF38AssertEqual("row 113+ commuting GL(4,3) order",
                GF38Row113Plus.commutingGeneralLinearOrder, 24261120);
GF38AssertEqual("row 113+ normaliser-factor intersection",
                GF38Row113Plus.normaliserIntersectionOrder, 2);
GF38AssertEqual("row 113+ full normaliser order",
                GF38Row113Plus.fullNormaliserOrder, 194088960);
GF38AssertEqual("row 113+ subgroup classes",
                GF38Row113Plus.subgroupClassCount, 2876);
GF38AssertEqual("row 113+ qualifying groups",
                Length(GF38Row113Plus.accepted), 18);

GF38Row113Minus := GF38EnumerateRow113("E-");;
GF38AssertEqual("row 113- extraspecial subgroup order", Size(GF38Row113Minus.core), 8);
GF38AssertEqual("row 113- local normaliser order",
                GF38Row113Minus.localNormaliserOrder, 48);
GF38AssertEqual("row 113- endomorphism-algebra dimension",
                GF38Row113Minus.endomorphismAlgebraDimension, 16);
GF38AssertEqual("row 113- commuting GL(4,3) order",
                GF38Row113Minus.commutingGeneralLinearOrder, 24261120);
GF38AssertEqual("row 113- normaliser-factor intersection",
                GF38Row113Minus.normaliserIntersectionOrder, 2);
GF38AssertEqual("row 113- full normaliser order",
                GF38Row113Minus.fullNormaliserOrder, 582266880);
GF38AssertEqual("row 113- subgroup classes",
                GF38Row113Minus.subgroupClassCount, 5993);
GF38AssertEqual("row 113- qualifying groups",
                Length(GF38Row113Minus.accepted), 107);

# Deduplicate the plus-type calculation on its own.  Its eighteen qualifying
# full inverse images represent eighteen classes, six of which also occur in
# the row-110 calculation.  The historical figures 12 and 45 count the new
# classes obtained when the plus- and minus-type calculations are adjoined,
# in that order, to the row-110 classes; they are not separate class counts
# for the two row-113 calculations.
GF38Row113PlusClasses := GF38NewClassList();;
GF38InsertGroups(GF38Row113PlusClasses,
                 GF38Row113Plus.accepted, "113 (E+)");
GF38AssertEqual("classes produced by row 113+",
                Length(GF38Row113PlusClasses.groups), 18);

GF38Rows110And113 := GF38NewClassList();;
GF38InsertGroups(GF38Rows110And113, GF38Row110.accepted, "110");
GF38AssertEqual("classes produced by row 110",
                Length(GF38Rows110And113.groups), 31);
GF38InsertGroups(GF38Rows110And113,
                 GF38Row113PlusClasses.groups, "113 (E+)");
GF38AssertEqual("classes after adjoining row 113+",
                Length(GF38Rows110And113.groups), 43);
GF38InsertGroups(GF38Rows110And113,
                 GF38Row113Minus.accepted, "113 (E-)");
GF38AssertEqual("classes produced by rows 110 and 113",
                Length(GF38Rows110And113.groups), 88);
GF38AssertEqual("row-113+ classes also produced by row 110",
    Length(Filtered(GF38Rows110And113.rowLabels, labels ->
        "110" in labels and "113 (E+)" in labels)), 6);
GF38Row113MinusClassCount := Length(Filtered(
    GF38Rows110And113.rowLabels, labels -> "113 (E-)" in labels));;
GF38Row113BothFormsCount := Length(Filtered(
    GF38Rows110And113.rowLabels, labels ->
        "113 (E+)" in labels and "113 (E-)" in labels));;
GF38Row113UnionCount := Length(Filtered(
    GF38Rows110And113.rowLabels, labels ->
        "113 (E+)" in labels or "113 (E-)" in labels));;

# Exact conjugacy now places every row-75 class in an independently complete
# row-110 or row-113 calculation.  The 2-cores in six cases have order 16 or
# 32 and occur in row 110, while those in two cases have order 8 and occur in
# row 113-.  The two order-64 cases also occur in row 110.
GF38Line75CoveragePositions := List(GF38Line75Groups,
    group -> GF38ClassPosition(GF38Rows110And113, group));;
if fail in GF38Line75CoveragePositions then
    Error("a row-75 class is absent from the row-110 and row-113 enumeration");
fi;
for GF38FileIndex in [1 .. 10] do
    GF38HoltYangPosition := GF38Line75CoveragePositions[GF38FileIndex];
    if GF38Line75TwoCoreData[GF38FileIndex].coreOrder = 8 then
        if not "113 (E-)" in
            GF38Rows110And113.rowLabels[GF38HoltYangPosition] then
            Error("a row-75 class with 2-core of order 8 is absent from row 113-");
        fi;
    elif not "110" in GF38Rows110And113.rowLabels[GF38HoltYangPosition] then
        Error("a row-75 class with larger 2-core is absent from row 110");
    fi;
od;
GF38AssertEqual("row-75 classes with 2-core of order 8 covered by row 113-",
    Length(Filtered([1 .. 10], index ->
        GF38Line75TwoCoreData[index].coreOrder = 8 and
        "113 (E-)" in GF38Rows110And113.rowLabels[
            GF38Line75CoveragePositions[index]])), 2);
GF38AssertEqual("row-75 classes with 2-core of order 16 or 32 covered by row 110",
    Length(Filtered([1 .. 10], index ->
        GF38Line75TwoCoreData[index].coreOrder in [16, 32] and
        "110" in GF38Rows110And113.rowLabels[
            GF38Line75CoveragePositions[index]])), 6);
GF38AssertEqual("row-75 classes with 2-core of order 64 covered by row 110",
    Length(Filtered([1 .. 10], index ->
        GF38Line75TwoCoreData[index].coreOrder = 64 and
        "110" in GF38Rows110And113.rowLabels[
            GF38Line75CoveragePositions[index]])), 2);
Print("Rows 110 and 113: 41, 18 and 107 qualifying full inverse images; ",
      "31 row-110 classes, ", Length(GF38Row113PlusClasses.groups),
      " row-113+ classes and ", GF38Row113MinusClassCount,
      " row-113- classes.  The two row-113 calculations have ",
      GF38Row113BothFormsCount, " classes in common and ",
      GF38Row113UnionCount, " classes in their union.  Adjoining the ",
      "row-113 calculations in the order E+, E- adds 12 and 45 classes ",
      "to the row-110 classes, giving 88 classes in all.\n");

# Form the union of every independently enumerated normaliser group and compare it in both
# directions with the 201 reference records.  The union does not grow beyond
# the 152 classes already found from rows 9, 75 and 117.
GF38AllEnumerated := GF38NewClassList();;
GF38InsertGroups(GF38AllEnumerated, GF38RemainingRows.groups, fail);
GF38InsertGroups(GF38AllEnumerated, GF38Row22Classes.groups, fail);
GF38InsertGroups(GF38AllEnumerated, GF38Rows110And113.groups, fail);
GF38AssertEqual("classes in the union of all nine row calculations",
                Length(GF38AllEnumerated.groups), 152);

for GF38Group in GF38AllEnumerated.groups do
    if GF38ClassPosition(GF38ReferenceClasses, GF38Group) = fail then
        Error("an enumerated class has no Holt--Yang or omitted reference");
    fi;
od;
for GF38Group in GF38ReferenceClasses.groups do
    if GF38ClassPosition(GF38AllEnumerated, GF38Group) = fail then
        Error("a Holt--Yang or omitted reference was not enumerated");
    fi;
od;

GF38DatasetRecords := function(classes)
    local records, i, entry;
    records := [];
    for i in [1 .. Length(classes.groups)] do
        entry := rec(index := i,
                     order := Size(classes.groups[i]),
                     generators := GeneratorsOfGroup(classes.groups[i]),
                     classInvariant := classes.invariants[i]);
        if Length(classes.rowLabels[i]) > 0 then
            entry.rowLabels := classes.rowLabels[i];
        fi;
        Add(records, entry);
    od;
    return records;
end;;

GF38Groups := rec(
    p := 3,
    d := 8,
    holtYangCount := 189,
    surplusCount := 12,
    totalReferenceCount := 201,
    referenceFileNames := GF38ReferenceFileNames,
    referenceFileCounts := GF38ReferenceFileCounts,
    references := GF38References,
    datasets := rec(
        remainingRows := rec(
            name := "remainingRows",
            count := 152,
            rowLabels := ["9 (E+)", "9 (E-)", "75",
                          "117 (E+)", "117 (E-)"],
            records := GF38DatasetRecords(GF38RemainingRows)),
        row117 := rec(
            name := "row117",
            count := 118,
            records := GF38DatasetRecords(GF38Row117Classes)),
        rows110And113 := rec(
            name := "rows110And113",
            count := 88,
            records := GF38DatasetRecords(GF38Rows110And113))));;

CheckReferenceData(GF38Groups);
GF38OutputPath := "../outputs/gf3_8_groups.g";;
PrintTo(GF38OutputPath, "GF38Groups := ", GF38Groups, ";\n");

Print("The nine GF(3)^8 row calculations contain exactly 152 GL(8,3)-classes.\n");
Print("The Holt--Yang files contain 140 of them; the row-22 enumeration ",
      "supplies the remaining twelve.\n");
QUIT_GAP(0);
