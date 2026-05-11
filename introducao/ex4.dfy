ghost function Fat(n: nat): nat
// Ghost indica que não gera código executável, é elemento de especificação apenas
{
  if n == 0
  then 1
  else n * Fat(n-1)
}

method Fatorial(n:nat)  returns (r:nat)
  ensures r == Fat(n)
{
  r := 1;
  var i := 0;
  while i < n
    invariant r == Fat(i) && i <= n
  {
    i := i + 1;
    r := r * i;
  }
}
