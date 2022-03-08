infixr 0 $
fun f $ a = f a
fun id x = x

fun flatMap f = List.concat o (map f)

fun enumerate L = ListPair.zip(List.tabulate(List.length L, id), L)

fun zipWith f ([], _) = []
  | zipWith f (_, []) = []
  | zipWith f (x::xs, y::ys) = f(x, y)::zipWith f (xs, ys)
  
fun foldl1 f (x::xs) = foldl f x xs
fun foldr1 f (x::xs) = foldr f x xs 

fun scanl f b [] = []
  | scanl f b (x::xs) = let val x' = f(x, b) in x' :: scanl f x' xs

fun scanr f b = #2 o foldr (fn (a, (x, y)) => (f(a, x), f(a, x)::y)) (b, [b])
fun scanri f b = #2 o foldr (fn (a, (x, y)) => (f(a, x), f(a, x)::y)) (b, [])

infix --
fun a -- b = List.tabulate(b - a + 1, fn i => i + a)

fun reduce f b V = 
  if Vector.length V = 0 then b
  else let
    fun reduce' i j =
      if i = j then f(Vector.sub(V, i), b)
      else let
        val mid = i + (j - i + 1) div 2
        val (l, r) = (reduce' i (mid - 1), reduce' mid j)
      in
        f(l, r)
      end
  in
    reduce' 0 (Vector.length V - 1)
  end
  
  
  fun scanl f b V = 
  let
    val x = ref b
  in
    Vector.map (fn y => !x before x := f(!x, y)) V
  end

fun memoize hf f = 
  let
    val cache = HashTable.mkTable hf (1000, Fail "No Element Found")
    fun memoized a = getOpt (HashTable.find cache a, let val r = f memoized a in r before HashTable.insert cache (a, r) end)
  in
    memoized
  end

fun Y f =
  let
    exception BlackHole
    val r = ref (fn _ => raise BlackHole)
    fun a x = !r x
    fun ta f = (r := f ; f)
  in
    ta (f a)
  end
  
  
  signature RANGE = 
  sig
    type range
    
    exception EmptyRange
    exception Loop
    exception EmptyStep
    
    exception NestedRange
    
    val to : int * int -> range
    val until : int * int -> range 
    
    val by : range * int -> range
    
    val for : range -> (int -> 'a) -> 'a
    
    val iterate : (int * 'a -> 'a) -> 'a -> range -> 'a
  end

structure Range :> RANGE = 
  struct
    datatype range =   
      inc of int * int 
    | exc of int * int 
    | stepUp of range * int 
    | stepDown of range * int
    
    exception EmptyRange
    exception Loop
    exception EmptyStep
    
    exception NestedRange
    
    infix to
    infix until
    infix by
    
    fun x to y = inc(x, y)
    
    fun x until y = if x = y then raise EmptyRange else exc(x, y)
    
    fun r by x = 
      case r of
        stepUp(_) => raise NestedRange
      | stepDown(_) => raise NestedRange
      | _ => 
          if x = 0 then raise EmptyStep 
          else if x < 0 then stepDown(r, x)
          else stepUp(r, x)
            
    
    fun for r f = 
      case r of
        inc(x, y) => 
          if x = y then f x 
          else if x > y then raise Loop
          else (f x; for (inc(x + 1, y)) f)
      | exc(x, y) => 
          if x + 1 = y then f x 
          else if x >= y then raise Loop
          else (f x; for (exc(x + 1, y)) f)
      | stepUp(inc(x, y), i) => 
          if x > y then raise Loop
          else if x = y orelse x + i > y then f x
          else (f x; for (stepUp(inc(x + i, y), i)) f) 
      | stepDown(inc(x, y), i) =>
          if x < y then raise Loop
          else if x = y orelse x + i < y then f x 
          else (f x; for (stepDown(inc(x + i, y), i)) f)
      | stepUp(exc(x, y), i) => 
          if x >= y then raise Loop
          else if x + i >= y then f x 
          else (f x; for (stepUp(exc(x + i, y), i)) f)
      | stepDown(exc(x, y), i) =>
          if x <= y then raise Loop
          else if x + i <= y then f x 
          else (f x; for (stepDown(exc(x + i, y), i)) f)
      | _ => raise NestedRange
      
    fun iterate f b r = 
     case r of
        inc(x, y) => 
          if x = y then f (x, b) 
          else if x > y then raise Loop
          else iterate f (f (x, b)) (inc(x + 1, y)) 
      | exc(x, y) => 
          if x + 1 = y then f (x, b)
          else if x >= y then raise Loop
          else iterate f (f (x, b)) (exc(x + 1, y)) 
      | stepUp(inc(x, y), i) => 
          if x > y then raise Loop
          else if x = y orelse x + i > y then f (x, b)
          else iterate f (f(x, b)) (stepUp(inc(x + i, y), i)) 
      | stepDown(inc(x, y), i) =>
          if x < y then raise Loop
          else if x = y orelse x + i < y then f (x, b)
          else iterate f (f(x, b)) (stepDown(inc(x + i, y), i))
      | stepUp(exc(x, y), i) => 
          if x >= y then raise Loop
          else if x + i >= y then f (x, b)
          else iterate f (f(x, b)) (stepUp(exc(x + i, y), i))
      | stepDown(exc(x, y), i) =>
          if x <= y then raise Loop
          else if x + i <= y then f (x, b)
          else iterate f (f(x, b)) (stepDown(exc(x + i, y), i))
      | _ => raise NestedRange
  end
  
open Range

infix to
infix until
infix by
