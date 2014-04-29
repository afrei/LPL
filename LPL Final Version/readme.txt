Adam Freilich
Final Project CIS 670
Spring 2013

LPL: A Toy Linear Programming Language

The bulk of this programming language is distributed in the five files types, parser, typechecker, eval and main (The other files contain the theorem prover which can be played around with in the ProverTypecheckerInterface file and were written by Mitchell Stern). I will discuss each in turn making special note of the real functions of interest. Afterwards I will exhibit the syntax of this language, show some examples and then suggest some fun things to try. 

*Types*

In this file I define the types Type and Exp which correspond to types and expressions. Their inductive definition matches the definitions in the lecture notes at http://www.cis.upenn.edu/~stevez/cis670/notes.pdf , save for the addition of annotations for abort and [] for the benefit of the typeChecher. Note that in addition to the standard show method given for expressions, there is a method display (of type Exp -> String) which makes expressions a bit more readable by using indentation. It is especially useful for nested case statements. The reason why it isn't the show method for expressions is that it doesn't play so nicely with the parser. 

*Parser* 

Using definitions for monadic parser combinators (taken from https://github.com/cthulhu314/ParsecExample/blob/master/parser.hs) I define the parsers for expressions and types. Potentially useful are: 

result         :: Parser a -> String -> Maybe a
typeParser     :: Parser Type
finalExpParser :: Parser Exp

These are enough to parse expressions.

*TypeChecker*

I elide the details of how the typeChecker works, but it suffices to note the following two things: 1) the act of typeChecking is just proof verification where expressions are interpreted as proof terms 2) the function

typeCheck :: Exp -> Maybe Type

will type check an expression returning either just it's verified type or Nothing. 

*Eval* 

The main function to be aware of defined in Eval is 

eval :: Exp -> Maybe Exp

which will reduce a well typed expression to its reduced from or may
fail in other cases. 

*Main*

The main uses the functions mentioned above to define a main which will prompt the user for expressions and, should they type check, prompt the user for a name. When the user no longer wants to add expressions she will be shown the registered expressions and be able to call them in expressions to be evaluated. After each expression is evaluated, the user will be prompted to add more expressions if they so desire and the process repeats. 

An example of running the main will be provided below. 

*Syntax* 

Generally types are 

0 | 1 |  T |  X | type -> type | type x type | type + type | type & type | !type 

where X stands in for any capital letter (which isn't T) examples of inhabited types include: 

  1 -> 1
  (A & B) -> A
  (A & B) -> B
  A -> (B + A)
  A -> (A + B)
  (A x B) -> ((T -> 1) -> A)
  A -> (B -> (B x A))
  A -> ((!(A -> B)) -> ((!(A -> C)) -> (B & C)))
  ((A + B) + (C + D)) -> (A + (B + (C + D)))

Try to parse (with the typeParser) one of the above strings, or one of your choosing. 
The following types are not inhabited: 
  
  A -> B
  A -> !A

They're not very different from the inhabited types (yet at least). 
The following are expressions corresponding to the inhabited types listed above:

fun {x1 : 1}.
({x1 : 1})

fun {x1 : A & B}.
(prj1 ({x1 : A & B}))

fun {x1 : A & B}.
(prj2 ({x1 : A & B}))

fun {x1 : A}.
(inj2 B + ({x1 : A}))

fun {x1 : A}.
(inj1 ({x1 : A}) + B)]

fun {x1 : A x B}.
(let {x2 : A} x {x3 : B} = ({x1 : A x B}) in
(fun {x4 : T -> 1}.
(let <> = (({x4 : T -> 1}) $ ([]  discarding :{x3 : B})) in
({x2 : A}))))

fun {x1 : A}.
(fun {x2 : B}.
(<{x2 : B} x {x1 : A}>))

fun {x1 : A}.
(fun {x2 : !(A -> B)}.
(let !{u3 : A -> B} = ({x2 : !(A -> B)}) in
(fun {x4 : !(A -> C)}.
(let !{u5 : A -> C} = ({x4 : !(A -> C)}) in
([(({u3 : A -> B}) $ ({x1 : A})) & (({u5 : A -> C}) $ ({x1 : A}))])))))

fun {x1 : (A + B) + (C + D)}.
(case {x1 : (A + B) + (C + D)} of
| inj1 {x2 : A + B}.(case {x2 : A + B} of
| inj1 {x3 : A}.(inj1 ({x3 : A}) + B + (C + D))
| inj2 {x4 : B}.(inj2 A + (inj1 ({x4 : B}) + C + D)))
| inj2 {x5 : C + D}.(case {x5 : C + D} of
| inj1 {x6 : C}.(inj2 A + (inj2 B + (inj1 ({x6 : C}) + D)))
| inj2 {x7 : D}.(inj2 A + (inj2 B + (inj2 C + ({x7 : D}))))))

because of the nested case statements, the latter may be easier to read when displayed: 

fun {x1 : (A + B) + (C + D)}.(  
  case {x1 : (A + B) + (C + D)} of  
    | inj1 {x2 : A + B}.(case {x2 : A + B} of  
      | inj1 {x3 : A}.(inj1 ({x3 : A}) + B + (C + D))
      | inj2 {x4 : B}.(inj2 A + (inj1 ({x4 : B}) + C + D))
    )
    | inj2 {x5 : C + D}.(case {x5 : C + D} of  
      | inj1 {x6 : C}.(inj2 A + (inj2 B + (inj1 ({x6 : C}) + D)))
      | inj2 {x7 : D}.(inj2 A + (inj2 B + (inj2 C + ({x7 : D}))))
    )
)

This should make most of the syntax clear. I feel the best presentation is probably a combination of looking at examples (like the above), looking at the definitions and show methods in the types file, and playing around with the given functions (some ways of doing so are outlined below). 

*Examples*

First, we use the parser to parse, typeCheck and reduce a complicated expression: 
>  result finalExpParser "((fun {x1 : 1 -> (1 -> 1)}.\n(fun {x2 : 1 x 1}.\n(let {x3 : 1} x {x4 : 1} = ({x2 : 1 x 1}) in\n((({x1 : 1 -> (1 -> 1)}) $ ({x3 : 1})) $ ({x4 : 1}))))) $ (fun {x1 : 1}.\n(fun {x2 : 1}.\n(let <> = ({x2 : 1}) in\n(let <> = ({x1 : 1}) in\n(<>)))))) $ (<<> x <>>)"
Just ((fun {x1 : 1 -> (1 -> 1)}.
(fun {x2 : 1 x 1}.
(let {x3 : 1} x {x4 : 1} = ({x2 : 1 x 1}) in
((({x1 : 1 -> (1 -> 1)}) $ ({x3 : 1})) $ ({x4 : 1}))))) $ (fun {x1 : 1}.
(fun {x2 : 1}.
(let <> = ({x2 : 1}) in
(let <> = ({x1 : 1}) in
(<>)))))) $ (<<> x <>>)
> let x = it
> x >>= typeCheck
Just 1
> x >>= eval
Just <>
> let y = fromJust x
> display y
"((fun {x1 : 1 -> (1 -> 1)}.(  \n  fun {x2 : 1 x 1}.(  \n    let {x3 : 1} x {x4 : 1} = ({x2 : 1 x 1}) in (  \n      ((({x1 : 1 -> (1 -> 1)}) $ ({x3 : 1})) $ ({x4 : 1})\n    )\n  )\n)) $ (fun {x1 : 1}.(  \n  fun {x2 : 1}.(  \n    let <> = ({x2 : 1}) in (  \n      (let <> = ({x1 : 1}) in (  \n        (<>\n      )\n    )\n  )\n))) $ (<<> x <>>)"
> putStrLn it
((fun {x1 : 1 -> (1 -> 1)}.(  
  fun {x2 : 1 x 1}.(  
    let {x3 : 1} x {x4 : 1} = ({x2 : 1 x 1}) in (  
      ((({x1 : 1 -> (1 -> 1)}) $ ({x3 : 1})) $ ({x4 : 1})
    )
  )
)) $ (fun {x1 : 1}.(  
  fun {x2 : 1}.(  
    let <> = ({x2 : 1}) in (  
      (let <> = ({x1 : 1}) in (  
        (<>
      )
    )
  )
))) $ (<<> x <>>)

Note the use of binds (we're in the maybe monad). Also, see that we apply a function of type (1 -> (1 -> 1)) -> ((1 x1) -> 1) to a function of type (1 -> (1 -> 1)) and then apply the result to <<> x <>> which is of type 1 x 1. It is not surprising that we get back <>. 

I now include an example of an instance of the repl: 

>Add expressions? (or quit?)
Y
>Please put in an expression:
<<> x <>>
>The expression has type
>1 x 1
>Is this ok?
Y
>What should we call this expression?
tens
>Add expressions? (or quit?)
Y
>Please put in an expression:
fun {x1 : 1 x 1} . (let {x2 : 1} x {x3 : 1} = {x1 : 1 x 1} in (<{x3 : 1} x {x2 : 1}>))
>The expression has type
>(1 x 1) -> (1 x 1)
>Is this ok?
Y
>What should we call this expression?
fxn
>Add expressions? (or quit?)
N
>Defined expressions:
>("fxn",fun {x1 : 1 x 1}.
>(let {x2 : 1} x {x3 : 1} = ({x1 : 1 x 1}) in
>(<{x3 : 1} x {x2 : 1}>)))
>("tens",<<> x <>>)
>Enter expression to evaluate
(fxn $ tens)
><<> x <>>
>Add expresions? (or quit?)
Q

*Further Exploration*

The file ProverTypecheckerInterface.hs provides the method typeToExp which has type Type -> Maybe Exp which uses an automated theorem prover to proved expressions (proofs) of a given type (proposition). While coding on ones own in LPL can be rewarding, it can also be frustrating as the parser, as it stands, provides no error messages. On the other hand, getting types to parse isn't so difficult and provides many interesting and complex expressions to play with. 

Another thing to try is to write a function which doesn't use variables linearly. It should parse but not typecheck. These should parse, but not typecheck. The theorem prover should not return such expressions, but by slightly modifying any typechecking expression, you ought to be able to produce one. 

I also suggest trying to break the typechecker and eval modes by purposely naming variables poorly. Breaking things is fun.  
