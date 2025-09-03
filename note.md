# HOLthing


A pure functional language which supports preconditions, postconditions, and arbitrary intermediate proof goals.

The language will generate HOL Light terms for every definition, automatically generating proof obligations based on code structure.


## Verifying partial definitions

For example, if you define a function partially over its type, you can add additional preconditional information to make 
missed cases impossible. This will incur a restraint at every callsite of the function however, and create a proof obligation that
the undefined cases are unreachable under the precondition.

```ml
let zip x y = match x, y with
    [], [] -> []
    | x::xs, y::ys -> x,y :: zip xs ys
    | [], _::_ -> ???
    | _::_, [] -> ???
    (* arbitrary semantics on these cases, fail or return empty list? It would be better if we had the option to leave it undefined *)
```

Because of the missing cases, the user could infer a constraint that would keep the more concise definition valid.

```ml
(* 🤔 This would be valid if we ensure that length x = length y *)
let zip x y = match x, y with
    [], [] -> []
    | x::xs, y::ys -> x,y :: zip xs ys
    (* missing cases here *)
```

So lets add that constraint so that the prover has access to it.

```ml
let zip x y = match x, y with
    [], [] -> []
    | x::xs, y::ys -> x,y :: zip xs ys
[%hol {|
    require `length x = length y`
    must `length xs = length ys` (* notice this as an enforcement of the precondition at our recursive call *)
|}]
```
Now that this has been added, we can take a peek at what HOL is seeing and what it has generated for us.

```
define `zip_soundness NIL NIL = NIL /\ 
        zip_soundness (CONS x xs) (CONS y ys) = CONS (x#y) (zip xs ys)`
```

Notice the missing cases in the definition. This is accepted by HOL, and you won't be able to simplify something like 'zip [1; 2] []'

HT would then require the proof of exhaustiveness under the condition

```
`length x = length y ==> 
    (x = [] /\ y = []) \/ 
    (?h t h' t'. x = CONS h t /\ y = CONS h' t')`
```

## Propagating proof information
There are a handful of keywords in HT that define which proof obligations are generated, which lemmas and assumptions are available in
a functions proof context, and how a function's current proof context should be interpreted at call sites.

### require

Require is supplied by the user and represents preconditions. Think of this as a way to request proof information from the caller.

### show

Show is supplied by the user and represents postconditions, or more generally, any lemma you want your current function to propagate to its call sites.
Think of this as a way to push proof information to the caller.


---

### have

Have is system generated and represents theorems that were proven in the callee that are now available for use.

### must

Must is system generated and represents the enforcement of preconditions at a call site.

### prove 

Prove is system generated and represents the enforcement of any verification conditions generated while defining the current function,
that must be proven for to accept the definition. This is often generated to ensure exhaustive handling under given requirements. Under normal exhaustive pattern
matching, this is discharged automatically, but in the case of partial definitions, it will require proof that undefined paths aren't accessible.

### measure

Measure is system generated and represents a termination measure for the current function.

---

Moving back to our example. We are requesting for a proof of length x = length y at the call site, but what if we want to offer some insight into the function
as well? If we were in a dependently typed language, we could encode something like the length of the resulting list in our type. Lets try that with HT


```ml
let zip x y = match x, y with
    [], [] -> []
    | x::xs, y::ys -> x,y :: zip xs ys
[%hol {|
    require `length x = length y`
    must `length xs = length ys`
    show `length (zip x y) = length y`
|}]
```

That was easy, we simply state our invariant as a HOL term. This of course will generate the proof obligation in the system for us to discharge.

```
`!x. !y. length x = length y ==> length (zip x y) = length y`
```

But we aren't limited to what we can cram into a type system. Since HOL acts as a separate oracle to our language, we can specify anything we want,
and watch it propagate to the call site in the same way a complex type system would. Lets define another random invariant, assuming we have some 
predicate P that we want to hold across zipping.

```ml
...
[%hol {|
    ...
    show `P x /\ P y ==> P (zip x y)`
|}]
```

Predicably this generates 

```
`!x. !y.  P x /\ P y ==> P (zip x y)`
```

Which is then available anywhere this function is called.


## The rules

There are some basic rules that govern how these concepts operate, most of which are what you would intuit.

### require

Say we have a predicate defined
```ml
let predicate z = true
```

And a function defined with a 'require'
```ml
let f x y = 
    if x > y then Foo else Bar

[%hol {|
    require `predicate x /\ predicate y` 
|}]

```

And we want to use 'f' in a new function. We will instantiate the required term with the arguments that it is called with
and generate a 'must' for the condition. The new definition 'g' will not be accepted until this is proven.

```ml
let g x y = 
    let a = x + 10 in
    let b = y - 99 in
    let foo = f a b in
    if foo = Foo then Bar else Baz
[%hol {|
    must `!x. !y. 
        let a = x + 10 in 
        let b = y - 99 in 
        predicate a /\ predicate b`
|}]

```

### Show

Show works as above, except it doesn't require a proof obligation as it was proved under its own assumptions in the callee

```ml
let f x y = 
    if x > y then Foo else Bar

[%hol {|
    show `predicate x /\ predicate y` 
|}]

```

And we want to use 'f' in a new function. We will instantiate the required term with the arguments that it is bound to 
and generate a 'have' for the condition.

```ml
let g x y = 
    let a = x + 10 in
    let b = y - 99 in
    let foo = f a b in
    if foo = Foo then Bar else Baz
[%hol {|
    have `!x. !y. 
        let a = x + 10 in 
        let b = y - 99 in 
        predicate a /\ predicate b`
|}] (* no obligations this is already proven *)
```

## The Language

HOL thing uses syntax similar to ML and Rust with some caviats. This should be obvious to use, major deviations are described below.

### Caviats

- No ML module system
- No mutable values
- No exceptions
- Functions have explicit type annotations
- No recursive function without 'fun'

### What we do have
- let bindings
- (mutually) recursive types and functions
- polymorphic functions
- if then else
- built in types matching HOL Light
- syntax for integrating proof data into function definitions

```
let x = Some(99)
let y = None

type option<'a> = Some('a) | None

def test(opt: option<int>) -> int {
    match opt {
        Some(n) => if n == 0 { 1 } else { n }
        None => 1
    }
}
requires `?n. $1 = None \/ $1 = Some n`
ensures `!n. test n != 0`

let res = test(y) + test(x)

let a = {
    let a_prime = 99
    let b = 1
    a_prime + b
}
```
