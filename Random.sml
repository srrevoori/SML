signature RANDOM = 
  sig
    val randReal : real * real -> real
    
    val randRange : int * int -> int

    val randString : int -> string
    
    val d : int -> unit -> int
    
    val flip : unit -> int
    
    val choice : 'a vector -> 'a
    
    val shuffle : 'a list -> 'a list
    
    val sample : 'a vector * int -> 'a list
    
    val choices : 'a vector -> int list -> int -> 'a list
    
    val ishuffle : 'a array -> unit
  end

structure Random :> RANDOM = 
  struct
    fun random () = 
      let
        val i = Time.toSeconds (Time.now())
        val x = i mod (Int.toLarge (valOf Int.maxInt))
        val y = Int.fromLarge x
        val z = Date.second (Date.fromTimeLocal (Time.now()))
      in
        Random.rand (y, z)
      end
    
    val r = random()
    
    fun randReal (x, y) = x + (y - x) * (Random.randReal r)
    
    fun randRange (x, y) = Random.randRange (x, y) r

    fun randString i = String.implode (List.tabulate(i, fn _ => Char.chr (randRange(97, 122))))
    
    fun d x () = randRange (1, x)

    fun flip () = randRange (0, 1)
    
    fun choice V = Vector.sub(V, randRange (0, (Vector.length V) - 1))

    fun mergeSort cmp [] = []
      | mergeSort cmp [x] = [x]
      | mergeSort cmp xs = 
          let
            fun split [] = ([], [])
              | split [x] = ([x], [])
              | split (x::y::xs) = 
                  let
                    val (L, R) = split xs
                  in
                    (x::L, y::R)
                  end
            fun merge ([], R) = R
              | merge (L, []) = L
              | merge (x::xs, y::ys) = 
                case  cmp (x, y) of
                  LESS => x::merge (xs, y::ys) 
                | GREATER => y::merge (x::xs, ys)
                | _ => y::x::merge (xs, ys)
            val (L, R) = split xs
          in
            merge (mergeSort cmp L, mergeSort cmp R)
          end
    
    fun shuffle L = 
      let
        val Lp = map (fn x => (x, randReal (0.0, 1.0))) L
        fun cmp ((_, x), (_, y)) = Real.compare (x, y)
      in
        map #1 (mergeSort cmp Lp)
      end
    
    fun quickselect cmp V k = 
      let
        val p = choice V
        val (lo, hi) = Vector.foldl (fn (a, (l, r)) => if cmp (a, p) = LESS then (a::l, r) else if cmp (a, p) = GREATER then (l, a::r) else (l, r)) ([], []) V
        val (l, r) = (Vector.fromList lo, Vector.fromList hi)
      in 
        if k < Vector.length l then quickselect cmp l k
        else if k < Vector.length V - Vector.length r then p
        else quickselect cmp r (k - Vector.length V + Vector.length r)
      end
      
    fun sample (V, k) = 
      if k = Vector.length V then Vector.foldl op:: [] V
      else let
        val Vp = Vector.map (fn x => (x, randReal(0.0, 1.0))) V
        fun cmp ((_, x), (_, y)) = Real.compare (x, y)
        val os = #2 (quickselect cmp Vp k)
      in
        Vector.foldl (fn ((a, p), b) => if p < os then a::b else b) [] Vp
      end
      
    fun choices V weights k = 
      let
        fun scanl f b [] = []
          | scanl f b (x::xs) = f(x, b) :: scanl f (f(x, b)) xs
        val prefixSums = Vector.fromList (scanl op+ 0 weights)
        val l = Vector.length prefixSums
        fun binarysearch nums (lo, hi) t = 
          if lo >= hi then lo
          else let
            val mid = lo + (hi - lo) div 2
          in
            if t <= Vector.sub(nums, mid) then binarysearch nums (lo, mid) t
            else binarysearch nums (mid + 1, hi) t
          end
        val max = Vector.sub(prefixSums, l - 1)
        fun loop 0 acc = acc
          | loop k acc = 
            let
              val i = binarysearch prefixSums (0, l) (randRange (1, max))
            in
              loop (k - 1) (Vector.sub(V, i) :: acc)
            end
      in
        loop k []
      end
    
    fun ishuffle A = 
      let
        open Range 
        open Array
        infix until
      in
        for(0 until length A - 1) 
          (fn i => 
            let 
              val j = randRange(0, i) 
              val temp = sub (A, j)
            in 
              (update(A, j, sub(A, i));
               update(A, i, temp))
            end)
      end
    
    fun quicksort L = 
      let
        val Ls = shuffle L
        fun qsort [] = []
          | qsort (x::xs) = qsort(List.filter (fn i => i < x) xs) @ (x :: qsort(List.filter (fn i => i >= x) xs))
      in
        qsort Ls
      end
    
    fun bogosort L = (* Expected O(n! * nlogn) *)
      let
        fun sorted [] = true
          | sorted [x] = true
          | sorted (x::y::xs) = x <= y andalso sorted(y::xs) 
      in
        if sorted L then L
        else bogosort (shuffle L)
      end

    fun freivald (A, B, C) k = (* O(kn^2) with probability of failure 2^-k*)
      let
        val n = List.length A
        fun multiply (A, x) = List.map (fn l => foldl (fn ((a1, a2), b) => a1 * a2 + b) 0 (ListPair.zip(l, x))) A
        fun compute () = 
          let
            val r = List.tabulate(n, fn _ => flip ())
            val Br = multiply (B, r)
            val ABr = multiply (A, Br)
            val Cr = multiply (C, r)
            val diff = map (fn (a,b) => a - b) (ListPair.zip(ABr, Cr))
          in    
            List.all (fn i => i = 0) diff
          end
      in
        if k = 0 then true 
        else if compute () then freivald (A, B, C) (k - 1)
        else false
      end
    
    fun findPi k = 
      let
        fun count f = foldl (fn (a, b) => if f a then b + 1 else b) 0
        val L = List.tabulate(k, fn _ => (randReal(~1.0,1.0), randReal(~1.0, 1.0)))
        val f = fn (x, y) => Math.sqrt (x * x + y * y) <= 1.0
      in
        4.0 * (Real.fromInt(count f L) / Real.fromInt(k) )
      end

    fun polynomialIdentityTest p F k = 
      if k < 0 then true
      else if p (choice F) = 0 then polynomialIdentityTest p F (k - 1)
      else false

    fun lazyselect (S, k) = (* Incorrect *)
      if k = 0 then Vector.foldl Int.min (valOf Int.maxInt) S
      else let
        val n = Real.fromInt (Vector.length S)
        val R = List.tabulate(Real.ceil (Math.pow(n, 0.75)), fn _ => choice S)
        val R = mergeSort R
        val x = (Real.fromInt k) * Math.pow(n, ~0.25)
        val l = Int.max(0, Real.floor (x - Math.sqrt n))
        val h = Int.min(Real.floor (Math.pow(n, 0.75)), Real.ceil (x + Math.sqrt n))
        val (a, b) = (List.nth (R, l) , List.nth (R, h) ) 
        fun rank x = Vector.foldl (fn (a, b) => if a < x then b + 1 else b) 1 S
        val (ranka, rankb) = (rank a, rank b)
        datatype rankcmp = A | B | BOTH
        val (P, cmp) = if k < Real.round (Math.pow(n, 0.25)) then 
                (Vector.foldl (fn (y, L) => if y <= b then y::L else L) [] S, B)
                else if k > Real.round (n - Math.pow(n, 0.25)) then
                (Vector.foldl (fn (y, L) => if y >= a then y::L else L) [] S, A)
                else (Vector.foldl (fn (y, L) => if y >= a andalso y <= b then y::L else L) [] S, BOTH)
      in
        if List.length P <= 4 * Real.round (Math.pow(n, 0.75)) + 2 then case cmp of 
          B => if k <= rankb then List.nth(mergeSort P, k - ranka + 1) else lazyselect (S, k)
        | A => if k >= ranka then List.nth(mergeSort P, k - ranka + 1) else lazyselect (S, k)
        | _ => if k <= rankb andalso k >= ranka then List.nth(mergeSort P, k - ranka + 1) else lazyselect (S, k)
        else lazyselect (S, k)
      end
    
  end




 