ghost predicate Sorted(a: array<int>)
  reads a
{
  //forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
  forall i :: 0 <= i < a.Length-1 ==> a[i] <= a[i+1]
}

method Main()
{
    var a := new int[3];
    a[0] := 1;
    a[1] := 3;
    a[2] := 5;
    assert Sorted(a);
}
