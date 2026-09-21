# Exact GL(8,3)-conjugacy comparison for the three independently enumerated
# comparison sets produced by gf3_8.g.

GF38CodeDirectory := Filename(DirectoryCurrent(), "");;
GF38OutputDirectory := Filename(Directory(GF38CodeDirectory), "../outputs");;
GF38GroupsFile := Filename(Directory(GF38OutputDirectory),
                           "gf3_8_groups.g");;
GF38MatricesFile := Filename(Directory(GF38OutputDirectory),
                             "gf3_8_conjugating_matrices.g");;

Read(Filename(Directory(GF38CodeDirectory),
              "gf3_8_conjugacy_methods.g"));;
Read(Filename(Directory(GF38CodeDirectory),
              "gf3_8_check_matrices.g"));;
GF38RequireAndRead(GF38GroupsFile);
GF38Check(IsBound(GF38Groups),
          "gf3_8_groups.g did not define GF38Groups");
CheckReferenceData(GF38Groups);

GF38WorkingDirectory := DirectoryTemporary();;
GF38Check(GF38WorkingDirectory <> fail,
          "could not create a temporary directory for the subsidiary calculations");
GF38Gap := GAPInfo.SystemCommandLine[1];;
GF38Check(IsExecutableFile(GF38Gap),
          "the current GAP executable cannot be started");
GF38GapOptions := [];;
GF38RootOptionPosition := Position(GAPInfo.SystemCommandLine, "-l");;
if GF38RootOptionPosition <> fail then
    Append(GF38GapOptions,
      [ "-l", GAPInfo.SystemCommandLine[GF38RootOptionPosition + 1] ]);
fi;
GF38Matrices := rec(remainingRows := List([1 .. 152], i -> fail),
                     row117 := List([1 .. 118], i -> fail),
                     rows110And113 := List([1 .. 88], i -> fail));;

for GF38DatasetName in [ "remainingRows", "row117", "rows110And113" ] do
    GF38Count := GF38Groups.datasets.(GF38DatasetName).count;
    GF38First := 1;
    while GF38First <= GF38Count do
        GF38Last := Minimum(GF38First + 3, GF38Count);
        GF38Stem := Concatenation(GF38DatasetName, "_",
                                  String(GF38First), "_",
                                  String(GF38Last));
        GF38ComparisonFile := Filename(GF38WorkingDirectory,
                                 Concatenation(GF38Stem, ".g"));
        GF38InstructionFile := Filename(GF38WorkingDirectory,
            Concatenation(GF38Stem, ".instruction.g"));
        PrintTo(GF38InstructionFile,
            "GF38CodeDirectory := \"", GF38CodeDirectory, "\";\n",
            "GF38GroupsFile := \"", GF38GroupsFile, "\";\n",
            "GF38Dataset := \"", GF38DatasetName, "\";\n",
            "GF38First := ", GF38First, ";\n",
            "GF38Last := ", GF38Last, ";\n",
            "GF38ComparisonFile := \"", GF38ComparisonFile, "\";\n",
            "Read(\"", Filename(Directory(GF38CodeDirectory),
                                  "gf3_8_compare_generators.g"),
            "\");\n");
        GF38ReturnCode := Process(Directory(GF38CodeDirectory), GF38Gap,
            InputTextNone(), OutputTextNone(),
            Concatenation(GF38GapOptions,
                [ "--quitonbreak", GF38InstructionFile ]));
        RemoveFile(GF38InstructionFile);
        GF38Check(GF38ReturnCode = 0 and
                  IsReadableFile(GF38ComparisonFile),
                  Concatenation("comparison failed for ",
                                GF38DatasetName, " items ",
                                String(GF38First), "--",
                                String(GF38Last)));
        if IsBoundGlobal("GF38GeneratorComparisons") then
            UnbindGlobal("GF38GeneratorComparisons");
        fi;
        GF38RequireAndRead(GF38ComparisonFile);
        GF38Check(IsBoundGlobal("GF38GeneratorComparisons"),
                  Concatenation(GF38ComparisonFile,
                                " does not define the requested subsidiary calculation"));
        GF38Computed := ValueGlobal("GF38GeneratorComparisons");
        GF38Check(GF38Computed.dataset = GF38DatasetName and
                  GF38Computed.start = GF38First and
                  GF38Computed.stop = GF38Last and
                  GF38Computed.itemCount = GF38Last - GF38First + 1 and
                  GF38Computed.datasetTotal = GF38Count and
                  GF38Computed.referenceTotal = 201 and
                  Length(GF38Computed.records) = GF38Computed.itemCount,
                  Concatenation(GF38ComparisonFile,
                                " has inconsistent bounds"));
        for GF38Record in GF38Computed.records do
            GF38Positive := Filtered(GF38Record.comparisons,
                                     c -> c.isConjugate);
            GF38Check(GF38Record.dataset = GF38DatasetName and
                      GF38Record.itemIndex >= GF38First and
                      GF38Record.itemIndex <= GF38Last and
                      Length(GF38Positive) > 0,
                      Concatenation(GF38ComparisonFile,
                                    " has inconsistent comparison data"));
            GF38Matrices.(GF38DatasetName)[GF38Record.itemIndex] :=
                rec(itemIndex := GF38Record.itemIndex,
                    referenceIndices := List(GF38Positive,
                                             c -> c.referenceIndex),
                    matrices := List(GF38Positive,
                                     c -> c.conjugatingMatrix));
        od;
        UnbindGlobal("GF38GeneratorComparisons");
        RemoveFile(GF38ComparisonFile);
        GASMAN("collect");
        GF38First := GF38Last + 1;
    od;
od;
GF38Check(not ForAny(Concatenation(GF38Matrices.remainingRows,
                                   GF38Matrices.row117,
                                   GF38Matrices.rows110And113),
                     x -> x = fail),
          "some generator comparisons are missing");
PrintTo(GF38MatricesFile,
        "GF38Matrices := ", GF38Matrices, ";\n");

GF38ConclusionLines := GF38CheckMatrices(GF38Groups, GF38Matrices);;
for GF38Line in GF38ConclusionLines do
    Print(GF38Line, "\n");
od;
QUIT_GAP(0);
