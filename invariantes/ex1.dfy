method Mult(x:nat, y:nat) returns (a:nat)
  ensures a == x * y
{
  var m:nat := x;
  var n:nat := y;
  a := 0;
  while m > 0
    invariant a + m * n == x * y
  {
    a := a + n;
    m := m - 1;
  }
}
