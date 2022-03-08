fun gcd(x, y) = if y = 0 then x else gcd(y, x mod y)

fun coprime (x, y) = gcd(x, y) = 1

fun fib n = 
  let
    val sq5 = Math.sqrt 5.0
    val gratiop = Math.pow((1.0 + sq5) / 2.0, Real.fromInt n) 
    val gration = Math.pow((1.0 - sq5) / 2.0, Real.fromInt n) 
  in
    round ((gratiop - gration) / sq5)
  end

fun binpow (x, y) = 
  if y = 0 then 1 
  else 
    let 
      val res = binpow(x, y div 2) 
    in 
      if y mod 2 = 0 then res * res else res * res * x 
    end

fun extendedEuclidean (x, y) = 
  if y = 0 then (x, 1, 0)
  else 
    let
      val (d, x1, y1) = extendedEuclidean(y, x mod y)
    in
      (d, y1, x1 - y1 * (x div y))
    end

fun modinv (a, m) = 
  let
    val (g, x, y) = extendedEuclidean(a, m)
  in
    if g = 1 then SOME ((x mod m + m) mod m) else NONE
  end

fun grayCode i = 
  let
    open Word
    infix >>
    infix xorb
    val x = fromInt i
    val one = fromInt 1
  in
    toInt (x xorb x >> one)
  end

fun graySequence n = 
  let
    open Word
    infix <<
    val x = fromInt n
    val one = fromInt 1
  in
    List.tabulate(toInt(one << x), grayCode)
  end

infix C
fun n C k = foldl (fn (i, res) => res * (n - k + i) div i) 1 (List.tabulate(k, fn i => i + 1))

fun catalan n = (2 * n) C n div (n + 1)

fun josephus (n, k) = if n > 1 then (josephus(n - 1, k) + k - 1) mod (n + 1) else 1
