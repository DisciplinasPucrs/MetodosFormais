ghost function Product(a: array<int>): int
  reads a
{
  ProductAux(a, 0, a.Length-1)
}

ghost function ProductAux(a: array<int>, from: nat, to: int): int
  requires to < a.Length
  reads a
{
  if from > to
  then 1
  else if from == to
       then a[to]
       else a[to] * ProductAux(a, from, to-1)
}

method ProductImpl(a: array<int>) returns (p:int)
  requires a.Length > 0
  ensures p == Product(a)
{
  p := 1;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant p == ProductAux(a, 0, i-1)
  {
    p := p * a[i];
    i := i + 1;
  }
}
