# Comparison of the matrix groups in the Holt--Yang files with the twelve
# additional classes on GF(3)^8.

if LoadPackage("irredsol") <> true then
    Error("The GAP package IrredSol is required.");
fi;

RequireEqual := function(description, found, expected)
    if found <> expected then
        Error(description, "\nexpected: ", expected, "\nfound: ", found);
    fi;
end;;

ReadRequiredFile := function(path)
    if not IsReadableFile(path) then
        Error("The required file is missing or unreadable: ", path);
    fi;
    Read(path);
end;;

MatrixConditionsHold := function(G, q, d)
    return IsMatrixGroup(G)
       and DimensionOfMatrixGroup(G) = d
       and ForAll(GeneratorsOfGroup(G),
                  matrix -> Length(matrix) = d
                     and ForAll(matrix, row -> Length(row) = d)
                     and ForAll(Flat(matrix), entry -> entry in GF(q)))
       and IsSolvableGroup(G)
       and IsIrreducibleMatrixGroup(G, GF(q));
end;;

LatexRowLabel := function(row)
    local suffix, number;
    if Length(row) >= 2 then
        suffix := row{[Length(row) - 1 .. Length(row)]};
        if suffix = "E+" or suffix = "E-" then
            number := row{[1 .. Length(row) - 2]};
            return Concatenation("$", number, "E^",
                suffix{[2]}, "$");
        fi;
    fi;
    return Concatenation("$", row, "$");
end;;

LatexInteger := function(number)
    local quotient, remainder;
    if number < 1000 then
        return String(number);
    fi;
    quotient := QuoInt(number, 1000);
    remainder := String(number - 1000 * quotient);
    while Length(remainder) < 3 do
        remainder := Concatenation("0", remainder);
    od;
    return Concatenation(LatexInteger(quotient), "\\,", remainder);
end;;

# The numbers below count records, not conjugacy classes.  The minus sign in
# the name Line1gpsm.g is historical: all twelve groups in that file have a
# plus-type extraspecial core.
DataFiles := [
 rec(file:="Line1gpsm.g",  variable:="Line1gps",  row:="1E+",  q:=3,  d:=16, count:=12, primitive:=12, tableCount:=12, tableMaximum:=15925248),
 rec(file:="Line3gps.g",   variable:="Line3gps",   row:="3",    q:=2,  d:=18, count:=40, primitive:=40, tableCount:=40, tableMaximum:=559872),
 rec(file:="Line9gpsp.g",  variable:="Line9gpsp",  row:="9E+",  q:=3,  d:=8,  count:=27, primitive:=27, tableCount:=27, tableMaximum:=18432),
 rec(file:="Line9gpsm.g",  variable:="Line9gpsm",  row:="9E-",  q:=3,  d:=8,  count:=71, primitive:=71, tableCount:=71, tableMaximum:=165888),
 rec(file:="Line10gps.g",  variable:="Line10gps",  row:="10",   q:=5,  d:=8,  count:=22, primitive:=22, tableCount:=22, tableMaximum:=331776),
 rec(file:="Line19gpsp.g", variable:="Line19gpsp", row:="19E+", q:=3,  d:=4,  count:=14, primitive:=14, tableCount:=14, tableMaximum:=2304),
 rec(file:="Line19gpsm.g", variable:="Line19gpsm", row:="19E-", q:=3,  d:=4,  count:=9,  primitive:=9,  tableCount:=9,  tableMaximum:=640),
 rec(file:="Line20gps.g",  variable:="Line20gps",  row:="20",   q:=5,  d:=4,  count:=22, primitive:=22, tableCount:=24, tableMaximum:=4608),
 rec(file:="Line21gpsp.g", variable:="Line21gpsp", row:="21E+", q:=7,  d:=4,  count:=16, primitive:=16, tableCount:=17, tableMaximum:=6912),
 rec(file:="Line22gps.g",  variable:="Line22gps",  row:="22",   q:=3,  d:=8,  count:=72, primitive:=65, tableCount:=72, tableMaximum:=18432),
 rec(file:="Line23gpsp.g", variable:="Line23gpsp", row:="23E+", q:=11, d:=4,  count:=4,  primitive:=4,  tableCount:=4,  tableMaximum:=11520),
 rec(file:="Line24gps.g",  variable:="Line24gps",  row:="24",   q:=13, d:=4,  count:=5,  primitive:=5,  tableCount:=5,  tableMaximum:=13824),
 rec(file:="Line25gps.g",  variable:="Line25gps",  row:="25",   q:=17, d:=4,  count:=4,  primitive:=4,  tableCount:=4,  tableMaximum:=18432),
 rec(file:="Line28gps.g",  variable:="Line28gps",  row:="28",   q:=5,  d:=8,  count:=3,  primitive:=3,  tableCount:=3,  tableMaximum:=55296),
 rec(file:="Line48gps.g",  variable:="Line48gps",  row:="48",   q:=2,  d:=6,  count:=7,  primitive:=7,  tableCount:=7,  tableMaximum:=1296),
 rec(file:="Line49gps.g",  variable:="Line49gps",  row:="49",   q:=7,  d:=3,  count:=4,  primitive:=4,  tableCount:=4,  tableMaximum:=1296),
 rec(file:="Line50gps.g",  variable:="Line50gps",  row:="50",   q:=13, d:=3,  count:=2,  primitive:=2,  tableCount:=2,  tableMaximum:=2592),
 rec(file:="Line51gps.g",  variable:="Line51gps",  row:="51",   q:=2,  d:=12, count:=8,  primitive:=8,  tableCount:=8,  tableMaximum:=12960),
 rec(file:="Line52gps.g",  variable:="Line52gps",  row:="52",   q:=19, d:=3,  count:=1,  primitive:=1,  tableCount:=1,  tableMaximum:=3888),
 rec(file:="Line53gps.g",  variable:="Line53gps",  row:="53",   q:=5,  d:=6,  count:=3,  primitive:=3,  tableCount:=10, tableMaximum:=10368),
 rec(file:="Line62gps.g",  variable:="Line62gps",  row:="62",   q:=3,  d:=2,  count:=2,  primitive:=2,  tableCount:=2,  tableMaximum:=48),
 rec(file:="Line63gps.g",  variable:="Line63gps",  row:="63",   q:=5,  d:=2,  count:=2,  primitive:=2,  tableCount:=2,  tableMaximum:=96),
 rec(file:="Line64gps.g",  variable:="Line64gps",  row:="64",   q:=7,  d:=2,  count:=2,  primitive:=2,  tableCount:=2,  tableMaximum:=144),
 rec(file:="Line65gps.g",  variable:="Line65gps",  row:="65",   q:=3,  d:=4,  count:=13, primitive:=11, tableCount:=13, tableMaximum:=384),
 rec(file:="Line66gps.g",  variable:="Line66gps",  row:="66",   q:=11, d:=2,  count:=2,  primitive:=2,  tableCount:=2,  tableMaximum:=240),
 rec(file:="Line67gps.g",  variable:="Line67gps",  row:="67",   q:=13, d:=2,  count:=2,  primitive:=2,  tableCount:=2,  tableMaximum:=288),
 rec(file:="Line68gps.g",  variable:="Line68gps",  row:="68",   q:=17, d:=2,  count:=3,  primitive:=3,  tableCount:=3,  tableMaximum:=384),
 rec(file:="Line69gps.g",  variable:="Line69gps",  row:="69",   q:=19, d:=2,  count:=2,  primitive:=2,  tableCount:=2,  tableMaximum:=432),
 rec(file:="Line71gps.g",  variable:="Line71gps",  row:="71",   q:=5,  d:=4,  count:=16, primitive:=16, tableCount:=16, tableMaximum:=1152),
 rec(file:="Line72gps.g",  variable:="Line72gps",  row:="72",   q:=3,  d:=6,  count:=2,  primitive:=2,  tableCount:=2,  tableMaximum:=1872),
 rec(file:="Line74gps.g",  variable:="Line74gps",  row:="74",   q:=7,  d:=4,  count:=7,  primitive:=7,  tableCount:=7,  tableMaximum:=2304),
 rec(file:="Line75gps.g",  variable:="Line75gps",  row:="75",   q:=3,  d:=8,  count:=10, primitive:=10, tableCount:=10, tableMaximum:=7680),
 rec(file:="Line117gps.g", variable:="Line117gps", row:="117",  q:=3,  d:=8,  count:=9,  primitive:=2,  tableCount:=9,  tableMaximum:=2304)
];;

RequireEqual("the number of Holt--Yang files", Length(DataFiles), 33);
RequireEqual("the number of Holt--Yang records",
             Sum(DataFiles, specification -> specification.count), 418);

recordTotal := 0;;
primitiveTotal := 0;;
row22Maximum := fail;;
latexRows := [];;

for specification in DataFiles do
    ReadRequiredFile(Concatenation("holt_yang_data/", specification.file));
    groups := ValueGlobal(specification.variable);
    RequireEqual(Concatenation("records in ", specification.file),
                 Length(groups), specification.count);
    filePrimitive := 0;
    fileMaximum := 0;
    for index in [1 .. Length(groups)] do
        G := groups[index];
        RequireEqual(
            Concatenation("matrix conditions for ", specification.file,
                          " record ", String(index)),
            MatrixConditionsHold(G, specification.q, specification.d), true);
        fileMaximum := Maximum(fileMaximum, Size(G));
        if IsPrimitiveMatrixGroup(G, GF(specification.q)) then
            filePrimitive := filePrimitive + 1;
        fi;
    od;
    RequireEqual(Concatenation("linearly primitive records in ",
                               specification.file),
                 filePrimitive, specification.primitive);
    RequireEqual(Concatenation("maximum group order in ", specification.file),
                 fileMaximum, specification.tableMaximum);
    if specification.row = "22" then
        row22Maximum := fileMaximum;
    fi;
    recordTotal := recordTotal + Length(groups);
    primitiveTotal := primitiveTotal + filePrimitive;
    Print(specification.file, ": ", Length(groups), " records, ",
          filePrimitive, " linearly primitive; maximum order ",
          fileMaximum, ".\n");
    Add(latexRows, Concatenation(
        LatexRowLabel(specification.row), " & \\texttt{",
        specification.file, "} & ", LatexInteger(specification.tableCount),
        " & ", LatexInteger(specification.count), " & ",
        LatexInteger(specification.tableMaximum), " & ",
        LatexInteger(fileMaximum),
        " \\\\"));
od;

RequireEqual("the Holt--Yang record total", recordTotal, 418);
RequireEqual("linearly primitive Holt--Yang records", primitiveTotal, 402);
RequireEqual("linearly imprimitive Holt--Yang records",
             recordTotal - primitiveTotal, 16);

ReadRequiredFile("gf3_8_additional_groups.g");
if not IsBound(GF38AdditionalGroups) then
    Error("gf3_8_additional_groups.g did not define GF38AdditionalGroups");
fi;
RequireEqual("additional GF(3)^8 records",
             Length(GF38AdditionalGroups), 12);

additionalPrimitive := 0;;
additionalMaximum := 0;;
for index in [1 .. Length(GF38AdditionalGroups)] do
    groupData := GF38AdditionalGroups[index];
    G := Group(groupData.generators);
    RequireEqual(
        Concatenation("matrix conditions for additional record ",
                      String(index)),
        MatrixConditionsHold(G, 3, 8), true);
    additionalMaximum := Maximum(additionalMaximum, Size(G));
    isPrimitive := IsPrimitiveMatrixGroup(G, GF(3));
    RequireEqual(
        Concatenation("linear primitivity of additional record ",
                      String(index)),
        isPrimitive, groupData.primitive);
    if isPrimitive then
        additionalPrimitive := additionalPrimitive + 1;
    fi;
od;

RequireEqual("linearly primitive additional records",
             additionalPrimitive, 9);
RequireEqual("linearly imprimitive additional records",
             Length(GF38AdditionalGroups) - additionalPrimitive, 3);
RequireEqual("maximum order among the additional classes",
             additionalMaximum, 2304);
RequireEqual("maximum order in the corrected row 22",
             Maximum(row22Maximum, additionalMaximum), 18432);

HoltYangPrimitiveClasses := 344;;
HoltYangImprimitiveClasses := 12;;
RequireEqual("Holt--Yang GL-class total",
             HoltYangPrimitiveClasses + HoltYangImprimitiveClasses, 356);
CorrectedPrimitiveClasses := HoltYangPrimitiveClasses + 9;;
CorrectedImprimitiveClasses := HoltYangImprimitiveClasses + 3;;
RequireEqual("linearly primitive GL-classes in the corrected collection",
             CorrectedPrimitiveClasses, 353);
RequireEqual("linearly imprimitive GL-classes in the corrected collection",
             CorrectedImprimitiveClasses, 15);
RequireEqual("corrected GL-class total",
             CorrectedPrimitiveClasses + CorrectedImprimitiveClasses, 368);

Print("Holt--Yang records: 402 linearly primitive; 16 linearly imprimitive.\n");
Print("Holt--Yang GL-classes: 344 linearly primitive; 12 linearly imprimitive.\n");
Print("Corrected GL-classes: 353 linearly primitive; 15 linearly imprimitive.\n");
Print("Total corrected GL-classes: 368.\n");
Print("\nLaTeX rows follow.  Columns:\n");
Print("row/type; file; Table 4.1 records; file records;\n");
Print("Table 4.1 maximum; calculated maximum.\n");
for line in latexRows do
    Print(line, "\n");
od;
QUIT;
