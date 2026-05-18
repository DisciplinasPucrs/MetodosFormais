method Main()
{
  var a := new int[5];
  //incializar todas posições em 0
  forall i | 0 <= i < a.Length
  {
    a[i] := 0;
  }
  var v := a[3];
  assert v == 0;
}

method Main2()
{
  var a := new int[5];
  //incializar todas posições em 0
  for i := 0 to a.Length
    invariant forall j:nat :: j < i ==> a[j] == 0
  {
    a[i] := 0;
  }
  var v := a[3];
  assert v == 0;
}
