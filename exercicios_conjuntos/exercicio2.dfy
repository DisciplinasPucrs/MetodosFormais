method FazAlgo(a: array<int>, n: int, e: int)
  //precondição para que n seja uma posição válida do array
  requires 0 <= n < a.Length
  //frame de escrita para indicar que o array será modificado
  modifies a
  //poscondição para indicar a alteração no array
  //até n (inclusive) com a quantidade do elemento "e" recém inserido incrementada
  ensures multiset(a[..n+1]) == multiset(a[..n]) + multiset{e}
{
    a[n] := e;
    //asserção que identifica a mudança ocorrida no array até a posição n (inlcui)
    //ou seja, até a posição n (não inclui) o array permanece o mesmo, e na posição n foi inserido o novo
    //elemento
    assert a[..n+1] == a[..n] + [e];
}