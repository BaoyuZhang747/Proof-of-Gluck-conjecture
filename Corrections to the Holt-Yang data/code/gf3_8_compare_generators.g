# Exact comparison of at most eight enumerated GF(3)^8 groups with all
# comparison records having the same necessary invariant.  This file is read
# automatically in the subsidiary GAP calculations started by
# gf3_8_conjugacy.g; it is not a separate calculation.

if not IsBound(GF38CodeDirectory) or
   not IsBound(GF38GroupsFile) or
   not IsBound(GF38Dataset) or
   not IsBound(GF38First) or
   not IsBound(GF38Last) or
   not IsBound(GF38ComparisonFile) then
    Error("the comparison parameters are not bound");
fi;
Read(Filename(Directory(GF38CodeDirectory),
              "gf3_8_conjugacy_methods.g"));;

if LoadPackage("irredsol") <> true then
    GF38Stop("the GAP package IrredSol is required");
fi;

datasetName := GF38Dataset;;
start := GF38First;;
stop := GF38Last;;
output := GF38ComparisonFile;;
GF38Check(datasetName = "remainingRows" or datasetName = "row117" or
          datasetName = "rows110And113",
          "the comparison-set name is not recognised");
GF38RequireAndRead(GF38GroupsFile);
GF38Check(IsBound(GF38Groups),
          "gf3_8_groups.g did not define GF38Groups");
referenceData := GF38Groups;;
CheckReferenceData(referenceData);
dataset := referenceData.datasets.(datasetName);;
GF38Check(1 <= start and start <= stop and stop <= dataset.count,
         "requested range is outside the comparison set");
GF38Check(stop - start + 1 <= 8,
         "one subsidiary calculation may contain at most eight enumerated groups");

# A comparison group is constructed only when its invariant agrees with that
# of an enumerated group, and is then retained for the rest of this calculation.
referenceGroups := List([1 .. 201], i -> fail);;
referenceContexts := List([1 .. 201], i -> fail);;
GetReference := function(index)
    local r, label;
    if referenceGroups[index] = fail then
        r := referenceData.references[index];
        label := Concatenation("reference ", String(index), " (", r.file,
                               "[", String(r.fileIndex), "])" );
        referenceGroups[index] := GF38MatrixGroupFromGenerators(
            r.generators, 3, 8, r.order, label);
        GF38Check(GF38ClassInvariant(referenceGroups[index]) = r.classInvariant,
                 Concatenation(label,
                               ": the recomputed characteristic-polynomial invariant differs from the stored value"));
        referenceContexts[index] := GF38ExactContext(referenceGroups[index]);
    fi;
    return referenceGroups[index];
end;;

results := [];;
for itemIndex in [start .. stop] do
    item := dataset.records[itemIndex];
    label := Concatenation(datasetName, " item ", String(itemIndex));
    Print("Comparing enumerated group ", itemIndex, " in ", datasetName,
          ", from row labels ", item.rowLabels, ", of order ",
          item.order, ".\n");
    poolGroup := GF38MatrixGroupFromGenerators(item.generators, 3, 8,
                                              item.order, label);
    classInvariant := GF38ClassInvariant(poolGroup);
    GF38Check(classInvariant = item.classInvariant,
             Concatenation(label,
                            ": recomputed characteristic-polynomial invariant differs from the stored value"));
    poolContext := GF38ExactContext(poolGroup);

    # Equality of the characteristic-polynomial invariant selects the full
    # equality block.  It proves nothing positive.
    invariantBlock := [];
    for i in [1 .. 201] do
        if referenceData.references[i].classInvariant = classInvariant then
            Add(invariantBlock, i);
        fi;
    od;
    GF38Check(Length(invariantBlock) > 0,
             Concatenation(label,
                           ": no reference invariant block exists"));
    comparisons := [];
    matchedIndices := [];
    for refIndex in invariantBlock do
        refGroup := GetReference(refIndex);
        coreExact := GF38ExactConjugacyViaTwoCore(refGroup, poolGroup, 3);
        if coreExact.isConclusive then
            exact := coreExact;
            argument := "O2-normaliser-quotient";
        else
            exact := GF38ExactConjugacyByAutomorphisms(referenceContexts[refIndex],
                                              poolContext, 3);
            argument := "automorphisms-and-module-intertwiners";
        fi;
        if exact.isConjugate then
            # The stored matrix sends the enumerated group to the comparison group.
            conjugatingMatrix := exact.conjugatingMatrixAtoB^-1;
            conjugatedGenerators := [];
            for g in GeneratorsOfGroup(poolGroup) do
                Add(conjugatedGenerators,
                    conjugatingMatrix^-1 * g * conjugatingMatrix);
            od;
            GF38Check(Group(conjugatedGenerators) = refGroup,
                      Concatenation(label,
                                    ": direct matrix substitution failed"));
            Add(matchedIndices, refIndex);
            comparison := rec(referenceIndex := refIndex,
                            isConjugate := true,
                            argument := argument,
                            conjugatingMatrix := conjugatingMatrix);
            if argument = "O2-normaliser-quotient" then
                comparison.coreOrder := exact.coreOrder;
                comparison.coreStructure := exact.coreStructure;
                comparison.homogeneousMultiplicity :=
                    exact.homogeneousMultiplicity;
                comparison.constituentDimension := exact.constituentDimension;
                comparison.coreEndomorphismDimension :=
                    exact.coreEndomorphismDimension;
                comparison.coreCentraliserOrder := exact.coreCentraliserOrder;
                comparison.normaliserOrder := exact.normaliserOrder;
                comparison.quotientOrder := exact.quotientOrder;
                comparison.quotientConjugacyResult :=
                    exact.quotientConjugacyResult;
            else
                comparison.twoCoreConclusion := coreExact.stage;
                comparison.coreOrderA := coreExact.coreOrderA;
                comparison.coreOrderB := coreExact.coreOrderB;
                comparison.homogeneousMultiplicityA :=
                    coreExact.homogeneousMultiplicityA;
                comparison.homogeneousMultiplicityB :=
                    coreExact.homogeneousMultiplicityB;
                comparison.coreEndomorphismDimensionA :=
                    coreExact.coreEndomorphismDimensionA;
                comparison.coreEndomorphismDimensionB :=
                    coreExact.coreEndomorphismDimensionB;
                comparison.outerCosetsTested := exact.outerCosetsTested;
                comparison.outerCosetsTotal := exact.outerCosetsTotal;
            fi;
            Add(comparisons, comparison);
            Print("  Conjugate to comparison record ", refIndex, ": ",
                  referenceData.references[refIndex].file, "[",
                  referenceData.references[refIndex].fileIndex,
                  "] matrix=substituted\n");
        else
            comparison := rec(referenceIndex := refIndex,
                            isConjugate := false,
                            argument := argument);
            if argument = "O2-normaliser-quotient" then
                comparison.twoCoreConclusion := exact.stage;
                if IsBound(exact.coreOrder) then
                    comparison.coreOrder := exact.coreOrder;
                    comparison.coreStructure := exact.coreStructure;
                    comparison.homogeneousMultiplicity :=
                        exact.homogeneousMultiplicity;
                    comparison.constituentDimension := exact.constituentDimension;
                    comparison.coreEndomorphismDimension :=
                        exact.coreEndomorphismDimension;
                    comparison.coreCentraliserOrder := exact.coreCentraliserOrder;
                    comparison.normaliserOrder := exact.normaliserOrder;
                    comparison.quotientOrder := exact.quotientOrder;
                else
                    comparison.coreOrderA := exact.coreOrderA;
                    comparison.coreOrderB := exact.coreOrderB;
                    comparison.coreStructureA := exact.coreStructureA;
                    comparison.coreStructureB := exact.coreStructureB;
                fi;
                comparison.quotientConjugacyResult :=
                    exact.quotientConjugacyResult;
            else
                comparison.twoCoreConclusion := coreExact.stage;
                comparison.outerCosetsTested := exact.outerCosetsTested;
            fi;
            Add(comparisons, comparison);
            Print("  Not conjugate to comparison record ", refIndex, ": ",
                  referenceData.references[refIndex].file, "[",
                  referenceData.references[refIndex].fileIndex, "]\n");
        fi;
    od;
    GF38Check(Length(comparisons) = Length(invariantBlock),
             Concatenation(label,
                           ": not every invariant-block record was tested"));
    GF38Check(Length(matchedIndices) > 0,
             Concatenation(label,
                           ": invariant block had no exact conjugate"));
    Add(results,
        rec(dataset := datasetName,
            itemIndex := itemIndex,
            itemOrder := item.order,
            classInvariant := classInvariant,
            invariantBlock := invariantBlock,
            conjugateReferenceIndices := matchedIndices,
            comparisons := comparisons));
od;

comparisonSet := rec(dataset := datasetName,
             start := start,
             stop := stop,
             itemCount := stop - start + 1,
             datasetTotal := dataset.count,
             referenceTotal := 201,
             records := results);;
PrintTo(output, "GF38GeneratorComparisons := ", comparisonSet, ";\n");
QUIT_GAP(0);
