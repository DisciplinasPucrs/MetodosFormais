ghost function Fat(n: nat): nat
{
  if n == 0 then 1 else n * Fat(n-1)
}

method Fatorial(n:nat)  returns (r:nat)
  ensures r == Fat(n)
{
  var i := 1;
  r := 1;
  while i <= n
    invariant 1 <= i <= n+1
    invariant r == Fat(i-1)
  {
    r := r* i;
    i := i + 1;
  }
}
