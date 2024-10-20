
##[

  ]##

import
  std / [pegs, cmdline, paths, files, strformat, strutils, sugar, sets,
         strscans, options, sequtils, algorithm]

{.experimental: "strictDefs".}
{.experimental: "strictFuncs".}


func commonPrefix(enumValueNames: seq[string]): string =
  ## Returns the prefix common to a set of enum value names.
  var others = enumValueNames
  let example = others.pop

  result = ""

  for index, exampleChar in example:
    let prefixFinished = others.anyIt:
      index > it.high or it[index] != exampleChar
    if prefixFinished:
      break
    else:
      result.add exampleChar

  # This catches the rare case that every value name happens to start with the
  # same character.
  #[E.g.:
      type
        cudaDeviceNumaConfig* = enum
          cudaDeviceNumaConfigNone = 0, <- would become `one`
          cudaDeviceNumaConfigNumaNode  <- would become `umaNode`
    ]#
  let firstCharIsSameOnAllValuesButNotPrefix = result[^2].isLowerAscii and
    result[^1].isUpperAscii and
    enumValueNames.mapIt(it.dup(removePrefix(result))).allIt(it[0].isLowerAscii)

  if firstCharIsSameOnAllValuesButNotPrefix:
    result = result[0..^2]

func nimIdentMatcher(ident: string): Peg =
  ## Returns a peg that matches the same an a Nim identifier of the input.
  sequence(term(ident[0]), termIgnoreStyle(ident[1..^1]),
    !charSet(Digits + Letters))

func abbrevEnum(enumTypeDesc: string): string =
  ## Returns the few letters that should be used as a prefix on impure enums.
  runnableExamples:
    var myParsedEnumTypeDesc = "cudaAsyncNotificationType"
    assert myParsedEnumTypeDesc.abbrevEnum == "ant"

    myParsedEnumTypeDesc = "cudaGraphInstantiateFlags"
    assert myParsedEnumTypeDesc.abbrevEnum == "gif"

  result = newStringOfCap(enumTypeDesc.len)

  var index = 0
  assert enumTypeDesc.scanp(index,
    *`LowercaseLetters`, # ignore library prefix
    +(`UppercaseLetters` -> result.add $_,  *`LowercaseLetters`))

  result = result.toLowerAscii


type
  EnumDecl = tuple
    nameOfType: string
    sizeDecider: Option[string]
    namesOfValues: seq[string]

proc parseEnumDecls(code: string): seq[EnumDecl] =
  ## Parses nim code and returns all the enum declarations present.
  let ast = peg"""enumDefs <- (@enumDef)*
  enumDef <- enumTypeDesc '*' (\s+ pragma)? \s+ '=' \s+ 'enum' \s+ (enumName enumValue? ',' (\s / someComment)+)* enumName enumValue?

  pragma <- '{.' \s* 'size:' \s+ 'sizeof(' sizeOfTypeDesc ').}'
  sizeOfTypeDesc <- \ident

  enumTypeDesc <- \ident
  enumName <- \ident
  enumValue <- ' = ' '-'? \d+ ('x' \d+)?

  singleLineCmt <- ('##' / '#') @\n
  multiLineCmt <- ('##[' / '#[') @(']##' / ']#')
  someComment <- multiLineCmt / singleLineCmt

  """

  func clear(self: var EnumDecl) =
    self.nameOfType = ""
    self.sizeDecider = none(string)
    self.namesOfValues = @[]

  var context: EnumDecl

  # Must have a temporary result variable for memory safety
  var enumDecls: typeOf(result) = @[]

  {.push warning[Uninit]: off.}
  let myPegEventParser = ast.eventParser:
    pkNonTerminal:
      leave:
        template thisMatch(): string =
          code[start .. start + length - 1]

        if length > 0:
          # Succesful match on a nonterminal (named) peg.
          case p.nt.name
          of "enumTypeDesc":
            context.nameOfType = thisMatch()
          of "sizeOfTypeDesc":
            context.sizeDecider = some(thisMatch())
          of "enumName":
            let alreadyCaptured = context.namesOfValues.len != 0 and
              context.namesOfValues[^1] ==  thisMatch()
            if not alreadyCaptured:
              context.namesOfValues.add thisMatch()
          of "enumDef":
            # Finished parsing the enum declaration.
            enumDecls.add context
            clear context

          else:
            discard

        else:
          case p.nt.name
          of "enumDef":
            # Failure parsing; not an enum declaration.
            clear context
          else:
            # Failure parsing some peg, not a failure yet.
            discard
  {.pop.}

  assert myPegEventParser(code) != -1
  result = enumDecls

func replaceFirstInstanceOf(
  s, sub: sink string; by: sink string = ""; start: Natural = 0): string =
    ## Replaces the first instance of the string `sub` with the string `by`.
    let firstChar = s.find(sub, start)
    if firstChar == -1:
      raise newException(ValueError, fmt"Couldnt find '{sub}'!")
    let lastChar = firstChar + sub.high

    result = s
    result.delete firstChar..lastChar
    result.insert by, firstChar


proc fixEnumValueNames*(code: sink string): string =
  ## This proc converts enums mostly into pure enums (removing the prefix in the
  ## process, but also switches the long-winded prefixes to short,
  ## abbreviated ones where appropriate.
  type ReplacePair = tuple
    pattern: Peg
    repl: string

  var replacePairs: seq[ReplacePair] = @[]
  var qualifiedEnums: seq[tuple[typeName: string, valueNames: seq[string]]] = @[]


  for (nameOfType, sizeDecider, namesOfValues) in parseEnumDecls(code):
    let notEnoughValues = namesOfValues.len < 2
    if notEnoughValues: continue

    let
      valuePrefix = namesOfValues.commonPrefix
      noCommonPrefix = valuePrefix.len == 0
    if noCommonPrefix: continue


    let prefixRemoved = namesOfValues.mapIt(it.dup(removePrefix(valuePrefix)))

    # This catches cases where an enum value name would start with some invalid
    # char for a nim identifier, like 0..9 or an underscore.
    let someInvalidValueName = prefixRemoved.anyIt:
      it[0] in Digits + {'_'}

    if someInvalidValueName:
      # do abbreviated prefix style enum, not pure
      let
        abreviatedNameOfType = nameOfType.abbrevEnum
        withAbrrevPrefix = prefixRemoved.mapIt(fmt"{abreviatedNameOfType}{it}")
      replacePairs.add zip(namesOfValues.mapIt(nimIdentMatcher it),
                           withAbrrevPrefix)
    else:
      # do pure enum style
      let pragmaInDecl = sizeDecider.isSome
      if pragmaInDecl:
        # we'll have to modify the already present pragma
        let typeDeclMatcher = sequence(term(nameOfType),
          peg" '*' \s+ '{.' ")
        replacePairs.add (typeDeclMatcher, fmt"{nameOfType}* {{.pure, ")
      else:
        # we'll add the pure pragma
        let typeDeclMatcher = sequence(term(nameOfType),
          peg" '*' \s+ '=' \s+ 'enum' ")
        replacePairs.add (typeDeclMatcher, fmt"{nameOfType}* {{.pure.}} = enum")

      # we have to fully qualify any references to the enum value identifiers
      let
        unqualified = namesOfValues.mapIt(nimIdentMatcher it)
        fullyQualified = prefixRemoved.mapIt(fmt"{nameOfType}.{it}")
      replacePairs.add zip(unqualified, fullyQualified)

      # save the pure enums to fix the declarations later
      qualifiedEnums.add (nameOfType, prefixRemoved)


  result = code.parallelReplace(replacePairs)

  # we replaced all instances of each pure enum's values with a fully qualified
  # version of it, like `myEnumTypeDesc.MyEnumName`, including inside the
  # declaration of this enum.
  # So lets fix that.

  while qualifiedEnums.len > 0:
    var valueNames: seq[string]
    let typeName: string
    (typeName, valueNames) = qualifiedEnums.pop

    let startOfDecl = result.find(fmt"{typeName}* {{.pure")

    # First, we must sort so that the longer names are replaced first.
    # E.g., `myEnumType.Value10` before `myEnumType.Value1`
    for valueName in valueNames.sorted(SortOrder.Descending):
      let qualified = fmt"{typeName}.{valueName}"
      result = result.replaceFirstInstanceOf(qualified, valueName, startOfDecl)



proc main =
  for arg in commandLineParams():
    assert (Path arg).fileExists, fmt "Bad argument! '{arg}' doesn't exist."

    let
      input = readFile(arg)
      mangled = input.fixEnumValueNames

    writeFile arg, mangled
    echo fmt"Mangled '{arg}'"



when isMainModule:
  main()