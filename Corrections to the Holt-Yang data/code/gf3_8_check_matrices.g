# Direct substitution of every supplied conjugating matrix.  The calculation
# checks full matrix-group equality, matches every enumerated group, prevents
# one reference record from being assigned twice within a comparison set,
# recovers all 201 records in the remaining-row comparison, and recovers the
# twelve omitted row-22 classes.

GF38CheckMatrices := function(groups, matrixData)
    local datasetNames, expectedCounts, referenceOwner, verifiedMatrices,
          datasetName, dataset, records, itemIndex, item, entry, position,
          referenceIndex, reference, group, referenceGroup, matrix,
          conjugatedGenerators, generator, missingReferences,
          line117Indices, missingLine117, omittedIndices;

    CheckReferenceData(groups);
    GF38Check(IsRecord(matrixData) and IsBound(matrixData.remainingRows) and
              IsBound(matrixData.row117) and
              IsBound(matrixData.rows110And113),
              "the conjugating-matrix data is incomplete");
    datasetNames := [ "remainingRows", "row117", "rows110And113" ];
    expectedCounts := rec(remainingRows := 152, row117 := 118, rows110And113 := 88);
    referenceOwner := rec(remainingRows := List([1 .. 201], i -> 0),
                          row117 := List([1 .. 201], i -> 0),
                          rows110And113 := List([1 .. 201], i -> 0));
    verifiedMatrices := rec(remainingRows := 0, row117 := 0, rows110And113 := 0);

    for datasetName in datasetNames do
        dataset := groups.datasets.(datasetName);
        records := matrixData.(datasetName);
        GF38Check(Length(records) = expectedCounts.(datasetName),
                  Concatenation(datasetName,
                                " has the wrong number of records"));
        for itemIndex in [1 .. Length(records)] do
            item := dataset.records[itemIndex];
            entry := records[itemIndex];
            GF38Check(entry.itemIndex = itemIndex and
                      IsList(entry.referenceIndices) and
                      IsList(entry.matrices) and
                      Length(entry.referenceIndices) = Length(entry.matrices)
                      and Length(entry.referenceIndices) > 0 and
                      Length(Set(entry.referenceIndices)) =
                          Length(entry.referenceIndices),
                      Concatenation(datasetName, " item ", String(itemIndex),
                                    " has invalid matrix data"));
            group := GF38MatrixGroupFromGenerators(
                item.generators, 3, 8, item.order,
                Concatenation(datasetName, " item ", String(itemIndex)));

            for position in [1 .. Length(entry.referenceIndices)] do
                referenceIndex := entry.referenceIndices[position];
                GF38Check(IsInt(referenceIndex) and
                          1 <= referenceIndex and referenceIndex <= 201,
                          Concatenation(datasetName, " item ",
                                        String(itemIndex),
                                        " has an invalid reference index"));
                reference := groups.references[referenceIndex];
                GF38Check(reference.classInvariant = item.classInvariant,
                          Concatenation(datasetName, " item ",
                                        String(itemIndex),
                           " lies outside the characteristic-polynomial invariant block"));
                referenceGroup := GF38MatrixGroupFromGenerators(
                    reference.generators, 3, 8, reference.order,
                    Concatenation("reference ", String(referenceIndex)));
                matrix := entry.matrices[position];
                GF38Check(IsList(matrix) and Length(matrix) = 8 and
                          ForAll(matrix,
                              row -> IsList(row) and Length(row) = 8) and
                          RankMat(matrix) = 8,
                          Concatenation(datasetName, " item ",
                                        String(itemIndex),
                                        " has an invalid matrix"));
                conjugatedGenerators := [];
                for generator in GeneratorsOfGroup(group) do
                    Add(conjugatedGenerators,
                        matrix^-1 * generator * matrix);
                od;
                GF38Check(Group(conjugatedGenerators) = referenceGroup,
                          Concatenation(datasetName, " item ",
                                        String(itemIndex),
                                        " fails direct matrix substitution"));
                verifiedMatrices.(datasetName) :=
                    verifiedMatrices.(datasetName) + 1;
                GF38Check(referenceOwner.(datasetName)[referenceIndex] = 0,
                          Concatenation(datasetName,
                                        " repeats reference ",
                                        String(referenceIndex)));
                referenceOwner.(datasetName)[referenceIndex] := itemIndex;
            od;
        od;
    od;

    GF38Check(verifiedMatrices.remainingRows = 201 and
              verifiedMatrices.row117 = 167 and
              verifiedMatrices.rows110And113 = 133,
              "the number of conjugating matrices is not 201, 167, 133");
    missingReferences := Filtered([1 .. 201],
                                  i -> referenceOwner.remainingRows[i] = 0);
    GF38Check(Length(missingReferences) = 0,
              Concatenation("references not recovered: ",
                            String(missingReferences)));
    line117Indices := Filtered([1 .. 201], i ->
        groups.references[i].kind = "holtYang" and
        groups.references[i].file = "Line117gps");
    GF38Check(Length(line117Indices) = 9,
              "the group data does not contain nine Line117 references");
    missingLine117 := Filtered(line117Indices,
                               i -> referenceOwner.row117[i] = 0);
    GF38Check(Length(missingLine117) = 0,
              Concatenation("Line117 references not recovered: ",
                            String(missingLine117)));
    GF38Check(ForAll(line117Indices, i ->
        IsBound(groups.datasets.row117.records[
            referenceOwner.row117[i]].rowLabels) and
        "117 (E+)" in groups.datasets.row117.records[
            referenceOwner.row117[i]].rowLabels),
        "a Line117 record is absent from the plus-type row-117 calculation");
    omittedIndices := Filtered([1 .. 201],
                               i -> groups.references[i].kind = "surplus");
    GF38Check(Length(omittedIndices) = 12 and
              ForAll(omittedIndices,
                     i -> referenceOwner.remainingRows[i] > 0),
              "the twelve omitted classes were not all recovered");

    return [
        "The three GF(3)^8 comparison sets have 152, 118 and 88 classes.",
        "All 189 Holt--Yang records and all twelve omitted classes are recovered; none lies outside the enumerated classes.",
        "All nine Line117 records occur in the plus-type row-117 calculation, and all twelve omitted row-22 classes are recovered.",
        "Direct substitution verifies the 501 conjugating matrices (201 + 167 + 133)."
    ];
end;;
