SetPrintFormattingStatus("*stdout*", false);;

VerifyEqual := function(description, found, expected)
    if found <> expected then
        Print("FAILED CHECK: ", description, "\n    expected: ", expected,
              "\n    found:    ", found, "\n");
        QUIT_GAP(1);
    fi;
    Print(description, ": ", found, "\n");
end;;

VerifyConjugation := function(description, groupA, groupB, matrix)
    local conjugated;
    conjugated := Group(List(GeneratorsOfGroup(groupA),
                             g -> matrix^-1 * g * matrix));
    VerifyEqual(description,
        Size(groupA) = Size(groupB) and conjugated = groupB, true);
end;;

Read("gf3_8_conjugacy_methods.g");
Read("corrected_data/verification_matrices.g");
mats := GF38CorrectedDataMatrices;;

Read("holt_yang_data/Line22gps.g");
originalLine22 := Line22gps;;
Read("corrected_data/Line22gps.g");
correctedLine22 := Line22gps;;
Read("holt_yang_data/Line117gps.g");

VerifyEqual("records in the published Line22gps.g", Length(originalLine22), 72);
VerifyEqual("records in the corrected Line22gps.g", Length(correctedLine22), 80);

removedIndices := mats.line22RemovedIndices;;
retainedIndices := Filtered([1 .. 72], i -> not i in removedIndices);;
VerifyEqual("retained Line22 records", Length(retainedIndices), 68);
VerifyEqual("records 1 to 68 of the corrected file equal the retained records, in order",
    ForAll([1 .. 68], j ->
        GeneratorsOfGroup(correctedLine22[j]) =
        GeneratorsOfGroup(originalLine22[retainedIndices[j]])),
    true);

for k in [1 .. 4] do
    VerifyConjugation(
        Concatenation("removed record ", String(removedIndices[k]),
            " is conjugate to Line117gps record ",
            String(mats.line117Counterparts[k]),
            " by the stored verified matrix"),
        originalLine22[removedIndices[k]],
        Line117gps[mats.line117Counterparts[k]],
        mats.line22ToLine117[k]);
od;

originalInvariants := List(originalLine22, GF38ClassInvariant);;
line117Invariants := List(Line117gps, GF38ClassInvariant);;
VerifyEqual("retained Line22 records sharing a class invariant with Line117gps.g",
    Number(retainedIndices, i -> originalInvariants[i] in line117Invariants), 0);

publishedInvariants := ShallowCopy(originalInvariants);;
for fileName in [ "Line9gpsp", "Line9gpsm", "Line75gps" ] do
    Read(Concatenation("holt_yang_data/", fileName, ".g"));
    Append(publishedInvariants, List(ValueGlobal(fileName), GF38ClassInvariant));
od;
Append(publishedInvariants, line117Invariants);
VerifyEqual("published records on GF(3)^8", Length(publishedInvariants), 189);

Read("../outputs/gf3_8_groups.g");
datasetRecords := GF38Groups.datasets.remainingRows.records;;
VerifyEqual("classes in the enumerated dataset", Length(datasetRecords), 152);
VerifyEqual("enumerated classes whose invariant is absent from every published file",
    Filtered([1 .. Length(datasetRecords)],
        i -> not datasetRecords[i].classInvariant in publishedInvariants),
    SortedList(mats.appendedDatasetIndices));

for k in [1 .. 12] do
    VerifyConjugation(
        Concatenation("appended record ", String(68 + k),
            " is conjugate to enumerated dataset record ",
            String(mats.appendedDatasetIndices[k]),
            " by the stored verified matrix"),
        correctedLine22[68 + k],
        Group(datasetRecords[mats.appendedDatasetIndices[k]].generators),
        mats.appendedToDataset[k]);
od;

correctedInvariants := List(correctedLine22, GF38ClassInvariant);;
VerifyEqual("distinct class invariants among the 80 corrected records",
    Length(Set(correctedInvariants)), 80);
VerifyEqual("corrected Line22 records sharing a class invariant with Line117gps.g",
    Number(correctedInvariants, v -> v in line117Invariants), 0);
VerifyEqual("orders of the twelve appended records",
    SortedList(List([69 .. 80], j -> Size(correctedLine22[j]))),
    [ 1152, 2304, 2304, 2304, 2304, 2304, 2304, 2304, 2304, 2304, 2304, 2304 ]);

Read("holt_yang_data/Line19gpsp.g");
originalP := Line19gpsp;;
Read("holt_yang_data/Line19gpsm.g");
originalM := Line19gpsm;;
Read("corrected_data/Line19gpsp.g");
correctedP := Line19gpsp;;
Read("corrected_data/Line19gpsm.g");
correctedM := Line19gpsm;;

VerifyEqual("records in the published Line19gpsp.g", Length(originalP), 14);
VerifyEqual("records in the published Line19gpsm.g", Length(originalM), 9);
VerifyEqual("records in the corrected Line19gpsp.g", Length(correctedP), 13);
VerifyEqual("records in the corrected Line19gpsm.g", Length(correctedM), 6);
VerifyEqual("corrected Line19gpsp equals the published file with record 14 removed",
    ForAll([1 .. 13], j ->
        GeneratorsOfGroup(correctedP[j]) = GeneratorsOfGroup(originalP[j])),
    true);
keptM := [ 1, 2, 3, 4, 5, 6 ];;
VerifyEqual("corrected Line19gpsm equals the published file with records 7, 8, 9 removed",
    ForAll([1 .. 6], j ->
        GeneratorsOfGroup(correctedM[j]) = GeneratorsOfGroup(originalM[keptM[j]])),
    true);

PickLine19 := function(side, i)
    if side = "p" then return originalP[i]; fi;
    return originalM[i];
end;;
for k in [1 .. 6] do
    pr := mats.line19Pairs[k];
    VerifyConjugation(
        Concatenation("Line19 identification ", pr[1], String(pr[2]),
            " = ", pr[3], String(pr[4]), " by the stored verified matrix"),
        PickLine19(pr[1], pr[2]), PickLine19(pr[3], pr[4]),
        mats.line19Matrices[k]);
od;

PrescribedTypes := function(G)
    local types, N, invCount;
    types := [];
    for N in NormalSubgroups(G) do
        if Size(N) = 32 and Size(Centre(N)) = 2
           and Size(DerivedSubgroup(N)) = 2
           and Size(FrattiniSubgroup(N)) = 2 then
            invCount := Number(N, x -> x <> One(N) and x^2 = One(N));
            if invCount = 19 then AddSet(types, "plus"); fi;
            if invCount = 11 then AddSet(types, "minus"); fi;
        fi;
    od;
    return types;
end;;

VerifyEqual("every corrected Line19gpsp record has a plus-type prescribed subgroup",
    ForAll(correctedP, G -> "plus" in PrescribedTypes(G)), true);
VerifyEqual("every corrected Line19gpsm record has a minus-type prescribed subgroup",
    ForAll(correctedM, G -> "minus" in PrescribedTypes(G)), true);
VerifyEqual("removed record 14 of Line19gpsp has no plus-type prescribed subgroup",
    PrescribedTypes(originalP[14]), [ "minus" ]);
VerifyEqual("removed records 7, 8, 9 of Line19gpsm have no minus-type prescribed subgroup",
    List([7, 8, 9], i -> PrescribedTypes(originalM[i])),
    [ [ "plus" ], [ "plus" ], [ "plus" ] ]);
VerifyEqual("the dual-type records p7 and p11 have prescribed subgroups of both types",
    List([7, 11], i -> PrescribedTypes(originalP[i])),
    [ [ "minus", "plus" ], [ "minus", "plus" ] ]);

line19Invariants := Concatenation(List(originalP, GF38ClassInvariant),
                                  List(originalM, GF38ClassInvariant));;
VerifyEqual("distinct classes among the 23 published row-19 records",
    Length(Set(line19Invariants)), 17);
correctedLine19Invariants := Concatenation(List(correctedP, GF38ClassInvariant),
                                           List(correctedM, GF38ClassInvariant));;
VerifyEqual("distinct classes among the 19 corrected row-19 records",
    Length(Set(correctedLine19Invariants)), 17);
VerifyEqual("the corrected row-19 files represent the same classes as the published files",
    Set(correctedLine19Invariants) = Set(line19Invariants), true);

Read("holt_yang_data/Line1gpsm.g");
originalLine1 := Line1gps;;
Read("corrected_data/Line1gpsp.g");
correctedLine1 := Line1gps;;
VerifyEqual("records in the corrected Line1gpsp.g", Length(correctedLine1), 12);
VerifyEqual("corrected Line1gpsp.g equals the published Line1gpsm.g record by record",
    ForAll([1 .. 12], j ->
        GeneratorsOfGroup(correctedLine1[j]) =
        GeneratorsOfGroup(originalLine1[j])),
    true);
VerifyEqual("every Line1 group has O_2 of order 512 with the plus-type involution count 271",
    ForAll(correctedLine1, function(G)
        local O2sub;
        O2sub := PCore(G, 2);
        return Size(O2sub) = 512 and Size(Centre(O2sub)) = 2
               and Size(DerivedSubgroup(O2sub)) = 2
               and Size(FrattiniSubgroup(O2sub)) = 2
               and Number(O2sub, x -> x <> One(O2sub) and x^2 = One(O2sub)) = 271;
    end), true);

Print("The directory corrected_data supplies the file-level corrections ",
      "established in the\naccompanying paper: Line22gps.g contains the 80 ",
      "row-22 classes; Line19gpsp.g and\nLine19gpsm.g contain the records ",
      "whose prescribed subgroups match the file type,\nwith the two ",
      "dual-type classes listed in both files; Line1gpsp.g carries the ",
      "corrected\nplus-type name with unchanged records.  Every removed ",
      "record is conjugate to a record\nthat remains, by the stored matrices ",
      "verified above.\n");
QUIT_GAP(0);
