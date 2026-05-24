ghost predicate sorted(s: seq<int>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

ghost function seqMax(s: seq<int>): int
  requires |s| > 0
  //ensures forall i :: 0 <= i < |s| ==> seqMax(s) >= s[i]
{
  if |s| == 1 then s[0] else if s[0] > seqMax(s[1..]) then s[0] else seqMax(s[1..])
}

method BubbleStep(a: array<int>, end: int)
  requires 1 <= end <= a.Length
  modifies a
  ensures multiset(a[..]) == multiset(old(a[..]))
  //ensures a[end - 1] == seqMax(old(a[..end]))
  ensures forall i :: 0 <= i < end - 1 ==> a[i] <= a[end - 1]
{
  var j := 0;
  while j < end - 1
    invariant 0 <= j <= end - 1
    invariant multiset(a[..]) == multiset(old(a[..]))
    invariant forall k :: 0 <= k < j ==> a[k] <= a[j]
  {
    if a[j] > a[j + 1] {
      a[j], a[j + 1] := a[j + 1], a[j];
    }
    j := j + 1;
  }
}

method BubbleSort(a: array<int>)
  modifies a
  ensures multiset(a[..]) == multiset(old(a[..]))
  ensures sorted(a[..])
{
  var n := a.Length;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant multiset(a[..]) == multiset(old(a[..]))
    invariant sorted(a[n - i ..])
    invariant forall k, l :: 0 <= k < n - i <= l < n ==> a[k] <= a[l]
  {
    BubbleStep(a, n - i);
    i := i + 1;
  }
}
