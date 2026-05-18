method teste()
{
  var a := new nat[5]; //a é do tipo array<nat>
  assert a[0] == 0;
  a[0] := 1;
  a[5] := 0;
  assert a.Length == 5;
  var b := new int[] [1,2,3]; //b é do tipo array<int>
}
