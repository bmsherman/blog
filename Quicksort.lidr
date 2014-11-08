> module Quicksort

> %hide Prelude.Nat.lte
> %default total

# Quicksort in Idris

The goal of this article is to build a version of quicksort in Idris that:
* produces evidence that the output list is sorted (with respect to a total ordering which is provided as input).
* is provably total in Idris. This means that recursive algorithms must be written in a form so that recursive calls recurse on structurally smaller arguments. Quicksort is an interesting case of an algorithm where it is not obvious what structure to recurse on (whereas insertion sort clearly recurses on linked lists and mergesort recurses on binary trees).
* produces evidence that the output list is a permutation of the input list. Many dependently-typed sorts don't bother to do this, so we will give it a try!

(Note: we will choose the first element of the list as the pivot, since it's easy!)

In the end, the type of our function will look like this:
```Idris
quicksort : TotalOrder a lte
          -> (xs : List a)
          -> (ys : List a ** (IsSorted lte ys, Permutation xs ys))
```
Of course, this has little meaning on its own without the definitions of some of those types (`TotalOrder`, `IsSorted`, and `Permutation`). So let's get started!

This article is available (almost verbatim) as a literate Idris document. The article is structured in a mathematical sort of way. We'll start with our data declarations (definitions) and simple properties about them, and then write a few helper functions (lemmas) before creating quicksort itself (the theorem).

## Data declarations

We begin be defining what we mean by ordering.
```Idris

> data PreOrder : (a : Type) -> (a -> a -> Type) -> Type where
>   PrO : {lte : a -> a -> Type} -- <=
>       -> ((x : a) -> (y : a) -> (z : a) -> lte x y -> lte y z -> lte x z) 
>          -- transitivity
>       -> PreOrder a lte
> 
> data TotalOrder : (a : Type) -> (a -> a -> Type) -> Type where
>   TotO : PreOrder a lte
>       -> ((x : a) -> (y : a) -> Either (lte y x) (lte x y))
>       -> TotalOrder a lte

```

These definitions are weaker than conventional notions of preorders and total orders. For example, conventionally, we might require that the `lte` relation of a preorder is reflexive. However, I didn't end up needing this property, or the properties I left out of my definition of total order, in order to define and construct quicksort, so I decided to leave them out for simplicity's sake.

The `Forall` datatype will allow us to state properties which hold for all elements of a list:
```Idris

> data Forall : (a -> Type) -> List a -> Type where
>   None : Forall p []
>   And : p x -> Forall p xs -> Forall p (x :: xs)

```
(Digression: Note that in the special case where `a = Type` and `p = id`, we may be more inclined to think of `Forall` as holding data rather than proofs, as we recover heterogenous vectors:
```Idris

> heterogenousVector : Forall id [Int, Bool, String]
> heterogenousVector = And 3 (And True (And "Hello" None))

```
)

Let's show some simple properties of `Forall` which we'll need to use later. Here are the natural generalizations of `map` and `zipWith`, respectively:
```Idris

> impList : (f : (x : a) -> p x -> q x)
>         -> (xs : List a) -> Forall p xs
>         -> Forall q xs
> impList f [] None = None
> impList f (x :: xs) (And px pxs) = And (f x px) (impList f xs pxs)
> 
> forallZipWith : (f : (x : a) -> p x -> q x -> r x)
>              -> (xs : List a) -> Forall p xs -> Forall q xs -> Forall r xs
> forallZipWith f [] None None = None
> forallZipWith f (x :: xs) (And px pxs) (And qx qxs) = 
>   And (f x px qx) (forallZipWith f xs pxs qxs)

```
(Note: we could have instead chosen to make the `(xs : List a)` argument implicit in either of these two functions, but we can't make the `(x : a)` that is bound in the function `f` to be implicit. Therefore, if the `xs` arguments were implicit, we'd need still need to bind the implicit `x` argument, and so I find the explicit style easier.) Next, we show that `Forall` plays nicely with list append:

```Idris

> propAppList : (ys : List a) -> (zs : List a)
>             -> Forall p (ys ++ zs)
>             -> (Forall p ys, Forall p zs)
> propAppList [] zs pzs = (None, pzs)
> propAppList (y :: ys) zs (And py pyszs) =
>   let (pys, pzs) = propAppList ys zs pyszs
>   in (And py pys, pzs)
> 
> propCatList : (ys : List a) -> Forall p ys
>            -> (zs : List a) -> Forall p zs
>            -> Forall p (ys ++ zs)
> propCatList [] _ zs pzs = pzs
> propCatList (y :: ys) (And py pys) zs pzs =
>   let pyszs = propCatList ys pys zs pzs in
>   And py pyszs

```

Defining `Forall` allows us to create a notion of lists sorted with respect to some binary relation:
```Idris

> data IsSorted : (a -> a -> Type) -> List a -> Type where
>   None1 : IsSorted lte []
>   And1 : {lte : a -> a -> Type} 
>        -> Forall (lte y) ys -> IsSorted lte ys -> IsSorted lte (y :: ys)

```
Note that we don't require `lte` to be a partial order in order to sort with respect to it. If we did require `lte` to be a partial order, we could equivalently define sorting in terms of simply ordering adjacent elements. This would make the "data" which comprises terms of type `IsSorted lte xs` to be linear in the size of `xs`, rather than quadratic as it is in this case. But the definition is a little simpler this way!

Now we define what it means to be a permutation:
```Idris

> data Permutation : List a -> List a -> Type where
>   Empty : Permutation [] []
>   Split : (xs : List a) -> (ys : List a) -> (zs : List a)
>         -> Permutation xs (ys ++ zs) -> Permutation (x :: xs) (ys ++ (x :: zs))
>   Comp : Permutation xs ys -> Permutation ys zs -> Permutation xs zs
>   Cat : Permutation xs zs -> Permutation ys ws -> Permutation (xs ++ ys) (zs ++ ws)

```
There are probably many ways to make a datatype representing permutations, but I chose these constructors because they very neatly reflect the structure of quicksort! `Split` corresponds to inserting the pivot into the middle of two sub-lists which have been recursively sorted, and `Cat` allows us to neatly integrate the permutations created by the recursive calls to quicksort.

Now, I am almost certain that the set of constructors for `Permutation` is not minimal: I think that `Cat` could be implemented as a function in terms of the other three constructors, and so it is redundant to have `Cat` as a constructor. However, I wasn't able to build such a function! Still, I imagine few people will doubt that `Permutation` satisfies their notion of permutations or worry that the `Cat` constructor makes the notion weaker.

If a property holds for all elements of a list, then it holds for all elements of any permutation of that list:
```Idris

> forallPerm : (xs : List a) -> Forall p xs
>            -> (ys : List a) -> Permutation xs ys
>            -> Forall p ys
> forallPerm [] None [] _ = None
> forallPerm _ (And px pxs) (ys ++ (x :: zs)) (Split xs ys zs permxsyszs) = 
>   let (pys, pzs) = propAppList ys zs (forallPerm xs pxs (ys ++ zs) permxsyszs) in
>   propCatList ys pys (x :: zs) (And px pzs)
> forallPerm (_ :: _) (And _ _) (ys ++ []) (Split _ _ _ _) impossible
> forallPerm xs {p} pxs zs (Comp {ys} permxy permyz) = 
>   forallPerm ys pys zs permyz
>   where
>   pys : Forall p ys
>   pys = forallPerm xs pxs ys permxy
> forallPerm (xs ++ ys) pxsys (zs ++ ws) (Cat permxszs permysws) = 
>   let (pxs, pys) = propAppList xs ys pxsys in
>   let pzs = forallPerm xs pxs zs permxszs in
>   let pws = forallPerm ys pys ws permysws in
>   propCatList zs pzs ws pws

```
We see that the previously defined `propAppList` and `propCatList` come in handy when we have the "concatenation" of two permutations.

Finally, we create a simple relation which describes when one list is no larger than another. We're basically counting with `List`s instead of `Nat`s, so this is the analogue of the `LTE` type constructor for `Nat`:

```Idris

> data LTEL : List a -> List a -> Type where
>   LTELNil  : LTEL [] xs
>   LTELCons : LTEL xs ys -> LTEL (x :: xs) (y :: ys)

```

This comes in handy for proving the totality of quicksort. When we make our recursive calls in quicksort, we will use this datatype to assure Idris that the lists in the recursive calls are no larger than the original list. `LTEL` satisfies some properties that we will need to use later:

```Idris

> loosenLTEL : LTEL xs ys -> LTEL xs (y :: ys)
> loosenLTEL LTELNil = LTELNil
> loosenLTEL (LTELCons prf) = LTELCons (loosenLTEL prf)
> 
> reflLTEL : (xs : List a) -> LTEL xs xs
> reflLTEL [] = LTELNil
> reflLTEL (x :: xs) = LTELCons (reflLTEL xs)
> 
> transLTEL : LTEL xs ys -> LTEL ys zs -> LTEL xs zs
> transLTEL LTELNil _ = LTELNil
> transLTEL (LTELCons prf) (LTELCons prf2) = LTELCons (transLTEL prf prf2)

```

## Helper functions

Partitioning a list is the workhorse of quicksort! We begin by creating a function to partition a list that will produce the evidence that we need for quicksort. We'll only need to partition based on ordering given by a total order, but we'll start with full generality:

```Idris

> partition' : {p : a -> Type} -> {q : a -> Type}
>            -> (f : (x : a) -> Either (p x) (q x))
>            -> (xs : List a)
>            -> (ys : List a ** 
>                 (zs : List a ** 
>                ( LTEL ys xs, LTEL zs xs
>                , Forall p ys, Forall q zs, Permutation xs (ys ++ zs) )
>               ))
> partition' f [] = ( [] ** ([] ** (LTELNil, LTELNil, None, None, Empty) ))
> partition' f (x :: xs) = 
>   let (ys ** (zs ** (ysSmall, zsSmall, pys, qzs, permxs))) = partition' f xs in
>   case f x of
>     Left  px => ( (x :: ys) ** (zs ** (LTELCons ysSmall, loosenLTEL zsSmall
>                 , And px pys, qzs, Split xs [] (ys ++ zs) permxs ) ))
>     Right qx => ( ys ** ((x :: zs) ** (loosenLTEL ysSmall, LTELCons zsSmall
>                 , pys, And qx qzs, Split xs ys zs permxs ) ))

```

We produce several pieces of evidence. First, we show that the two output lists must each be no larger than the input list. Of course, a stronger statement is true: the size of the two output lists appended together is exactly the size of the input list (and that is very strongly hinted at the fact that we produce a `Permutation` from the input list to the concatenation of the output lists). We don't need to know this, however, to assure Idris that quicksort terminates. But the difference between these two statements means everything in terms of computational complexity. If we only knew that each of the two output lists were no larger than the input list, we'd only be assured that the complexity of quicksort was `O(2^n)`; the stronger property tells us that the complexity is at worst quadratic.

We also show that the relevant properties that the partition was based on hold for the two output lists, which is quite straightforward. Finally, we show that the concatenation of the two output lists is a permutation of the input list. Fortunately, `Split` is exactly what we need for `::` case.

For quicksort, where `partition` is used to split a list based on ordering compared to a pivot element, it's nice to produce an additional proof object which tells us that every element in list of "smaller" elements is no greater than every element in the list of "larger" elements. We need a total order here, for two reasons:
* Only total orders assure us that either `x <= y` or `y <= x` will be the case
* The ordering relation must be transitive for the "smaller" elements to be no greater than the "larger" elements; we use the property 
```
s <= p && p <= l    ==>    s <= l
```
where `s` is a "smaller" element, `p` is the pivot element, and `l` is a larger element.

```Idris

> ordPartition : TotalOrder a lte
>              -> (pivot : a) -> (xs : List a)
>              -> (ys : List a ** 
>                   (zs : List a **
>                ( LTEL ys xs, LTEL zs xs
>                , Forall (flip lte pivot) ys, Forall (lte pivot) zs
>                , Forall (\y => Forall (lte y) zs) ys, Permutation xs (ys ++ zs))
>                ))
> ordPartition {lte} (TotO (PrO transt) eith) pivot xs = 
>   let (ys ** (zs ** (ysSmall, zsSmall, pys, qzs, perm))) = 
>             partition' {p=flip lte pivot} {q=lte pivot} (eith pivot) xs in
>   (ys ** (zs ** (ysSmall, zsSmall, pys, qzs, lem2 zs qzs ys pys , perm) ))
>   where
>   lem2 :  (zs : List a) -> Forall (lte pivot) zs
>        -> (ys : List a) -> Forall (flip lte pivot) ys 
>        -> Forall (\y => Forall (lte y) zs) ys
>   lem2 zs xltzs = impList (\y, yltx => lem y yltx zs xltzs)
>     where
>     lem : (y : a) -> lte y pivot -> (zs : List a) 
>         -> Forall (lte pivot) zs -> Forall (lte y) zs
>     lem y yltx = impList (\z, xltz => transt y pivot z yltx xltz)

```
The only real work we're doing on top of `partition'` is producing that above-mentioned evidence. The evidence is a `Forall` of a `Forall`, which is like a list of lists. Accordingly, to produce the evidence, we use `lem2`, which uses an `impList` within an `impList`, which is very much like `map (\x => map (\y => ...))`. 

So `ordPartition` is key to the "divide" part of the quicksort algorithm. The "merge" part of quicksort is fairly simple (just append the two result lists together!), but its correctness depends on the following property:

```Idris

> partSorted : (xs : List a) -> IsSorted lte xs
>            -> (ys : List a) -> IsSorted lte ys
>            -> Forall (\x => Forall (lte x) ys) xs
>            -> IsSorted lte (xs ++ ys)
> partSorted [] _ ys sortys _ = sortys
> partSorted (x :: xs) {lte} (And1 xltxs sortxs) ys sortys (And xltys xsltys) =
>   And1 xltxsys sortxsys
>   where
>   sortxsys : IsSorted lte (xs ++ ys)
>   sortxsys = partSorted xs sortxs ys sortys xsltys
>   xltxsys : Forall (lte x) (xs ++ ys)
>   xltxsys = propCatList xs xltxs ys xltys

```

## Putting it all together!

We now have all the pieces we need for creating quicksort. However, as mentioned previously, in order to convince Idris that quicksort is total, it must be written in a structurally recursive form; all recursive calls must recurse on strict substructures of one of the arguments. Unfortunately, quicksort does not obviously have this form: suppose we call quicksort on `x :: xs`. The `x` becomes the pivot, and then `xs` is partitioned over that pivot into, say, `ys` and `zs`. The partitioning has chopped `xs` up so that it is not guaranteed (and actually very unlikely) that `ys` or `zs` is the same as or a substructure of `xs`, and so we do not know that `ys` or `zs` is a substructure of `x :: xs`. 

Of course, what we'd like to do is somehow recurse using the `xs` as the substructure of `x :: xs`, since the `xs` is at least as "big" as both `ys` and `zs`. But `xs` has no role in the recursive call to quicksort! So we'll create one. Essentially, we'll just use the trick of having an accumulating parameter. This accumulating parameter won't actually be relevant to the computation. Instead, the accumulating parameter will just be an upper bound on the amount of computation remaining; therefore, it should be a list which is at least as "big" as the list which is being sorted! So we'll need another additional argument which witnesses that fact. The `LTEL` datatype which we defined earlier reifies this notion of bigger/smaller.

```Idris

> quicksortHelper : TotalOrder a lte
>                 -> (xs : List a)
>                 -> (listBound : List a)
>                 -> (xsSmall : LTEL xs listBound)
>                 -> (ys : List a ** (IsSorted lte ys, Permutation xs ys))
> quicksortHelper       totorder [] _ _ = ([] ** (None1, Empty) )
> quicksortHelper {lte} totorder (x :: xs) (xB :: xsB) (LTELCons xsSmall) = 
>   -- partition
>   let (ys ** (zs ** (ysSmall, zsSmall, ysltx, xltzs, ysltzs, perm))) = 
>         ordPartition totorder x xs in
>   -- recursive calls
>   let (ys' ** (sortedys', permysys')) = 
>         quicksortHelper totorder ys xsB (transLTEL ysSmall xsSmall) in
>   let (zs' ** (sortedzs', permzszs')) = 
>         quicksortHelper totorder zs xsB (transLTEL zsSmall xsSmall) in 
> 
>   -- show our result list is sorted
>   let ysltzs' : Forall (\y => Forall (lte y) zs') ys
>          = impList (\y, yltzs => forallPerm zs yltzs zs' permzszs') ys ysltzs in
>   let ys'ltzs' : Forall (\y => Forall (lte y) zs') ys'
>                = forallPerm ys ysltzs' ys' permysys' in
>   let ys'ltx : Forall (flip lte x) ys'
>              = forallPerm ys ysltx ys' permysys' in
>   let ys'ltxzs' : Forall (\y => Forall (lte y) (x :: zs')) ys' 
>                 = forallZipWith (\y => And) ys' ys'ltx ys'ltzs' in
>   let sortedxzs' : IsSorted lte (x :: zs')
>                  = And1 (forallPerm zs xltzs zs' permzszs') sortedzs' in
>   let sortedys'xzs' : IsSorted lte (ys' ++ x :: zs')
>                     = partSorted ys' sortedys' (x :: zs') sortedxzs' ys'ltxzs' in
> 
>   -- show our result list is a permutation of the original list
>   let perm' : Permutation (ys ++ zs) (ys' ++ zs')
>             = Cat permysys' permzszs' in
>   let perm'' : Permutation xs (ys' ++ zs')
>              = Comp perm perm' in
>   let permAll : Permutation (x :: xs) (ys' ++ x :: zs')
>               = Split xs ys' zs' perm'' in
> 
>   -- put it all together!
>   ((ys' ++ (x :: zs')) ** ( sortedys'xzs', permAll) )

```

And finally, we can define quicksort by simply initializing the accumulating parameter:
```Idris

> quicksort : TotalOrder a lte
>           -> (xs : List a)
>           -> (ys : List a ** (IsSorted lte ys, Permutation xs ys))
> quicksort totorder xs = quicksortHelper totorder xs xs (reflLTEL xs)

```

## Example with `Nat`

Let's run it! We can easily create a total order for `Nat` based on the `LTE` relation:
```Idris

> natLTETrans : (n, m, o : Nat) -> LTE n m -> LTE m o -> LTE n o
> natLTETrans Z _ _ _ _ = lteZero
> natLTETrans (S n) (S m) (S o) (lteSucc p) (lteSucc q) = lteSucc (natLTETrans n m o p q)
> 
> natLTEEith : (x, y : Nat) -> Either (LTE y x) (LTE x y)
> natLTEEith Z _ = Right lteZero
> natLTEEith _ Z = Left lteZero
> natLTEEith (S n) (S m) with (natLTEEith n m)
>   | Right x = Right (lteSucc x)
>   | Left y = Left (lteSucc y)
> 
> totNat : TotalOrder Nat LTE 
> totNat = TotO (PrO natLTETrans) natLTEEith

```

Now, at the REPL, we can try, for example:
```
*Quicksort> quicksort totNat [5,3,2,6,1]
([1, 2, 3, 5, 6] ** < blah blah blah >)
```

## Comments

I like the type of `quicksort`: if you don't care about either of the proofs, you can simply discard them and end up with a list whose type is exactly the same as that of the input list. The `IsSorted` and `Permutations` are nice and separate as well.

I have not paid any attention here to which terms ought to be computed and which should be erased for compilation. I guess it probably depends on your point of view; might you wish to examine the proof objects at runtime? If so, the efficiency of the proofs may become important as well; we may wish to, for example, redefine `IsSorted` so that it doesn't take memory quadratic in the size of the list!

## Other sorts of sorts

[McBride 2014](https://personal.cis.strath.ac.uk/conor.mcbride/Pivotal.pdf) presents some very interesting ideas about creating data structures which maintain ordering of their elements. The article primarily focuses on building generic element-holding structures which guarantee order invariants (such as binary search trees). As McBride points out, a sorted list is just a special case of a binary search tree that is completely right-leaning! With this point of view, getting a list from a binary search tree consists merely of rebalancing the tree until it is a list.

McBride also points on that David Turner noticed that quicksort is essentially the same thing as building a binary search tree and then flattening it (i.e., [tree sort](http://en.wikipedia.org/wiki/Tree_sort)). If we insert elements into a binary search tree starting from the front of the list for tree sort, then the tree sort's nodes will correspond directly to the pivots of quicksort (where we take the first element as the pivot), and the exact same comparisons will be made. However, the order of evaluation may be different. It is easy to convince typecheckers that tree-sort terminates: insertion into a tree is structurally recursive, and traversing a tree is structurally recursive. Inserting each element of the list structurally recurses down the list. So tree sort is another viable way of implementing a quicksort-like algorithm without having to worry so much about proving termination. Tree-sort also yields a natural way of providing evidence of ordering: the type of each sub-tree maintains the range which its elements occupy, and two trees may be merged if a pivot element lies between the two ranges, and the resulting range goes from the minimum of the left tree to the maximum of the right. Viewing a list a poorly balanced tree, this would mean that the order invariant to keep track of would simply be the minimum of the list. This is a nice way to show sortedness; it could easily replace the `IsSorted` type used here, and perhaps it would make the construction of the quicksort here a little more straightforward.

McBride has an interesting opinion on providing evidence that sorting functions only permute their inputs:
| Having developed a story about ordering invariants to the extent that our favourite sorting algorithms silently establish them, we still do not have total correctness intrinsically. What about permutation? It has always maddened me that the insertion and flattening operations manifestly construct their output by rearranging their input: the proof that sorting permutes should thus be by inspection. Experiments suggest that many sorting algorithms can be expressed in a domain specific language whose type system is linear for keys. We should be able to establish a general purpose permutation invariant for this language, once and for all, by a logical relations argument. We are used to making sense of programs, but it is we who make the sense, not the programs. It is time we made programs make their own sense.

I think this is a great idea! It certainly seems cleaner than having to define what a permutation is for every data structure which you wish to rearrange.
