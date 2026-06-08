datatype Option<T> = None | Some(T)

ghost predicate Menor(a:set<int>, b:set<int>) {
  forall x, y :: x in a && y in b ==> x < y
}

ghost function Uniao<Data>(m:map<int, Data>, n:Nodo?<Data>): map<int, Data>
  reads n
{
  if n == null
  then m
  else m + n.Mapa
}

class Nodo<T>
{
  //Abstração
  ghost var Mapa:map<int,T>
  ghost var Repr:set<object>
  //Implementação
  var chave:int
  var valor:T
  var esq:Nodo?<T>
  var dir:Nodo?<T>

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {
    && this in Repr
    && (esq != null ==>
      && esq in Repr
      && esq.Repr <= Repr
      && this !in esq.Repr
      && esq.Valid()
      && Menor(esq.Mapa.Keys, {chave})
    )
    && (dir != null ==>
      && dir in Repr
      && dir.Repr <= Repr
      && this !in dir.Repr
      && dir.Valid()
      && Menor({chave}, dir.Mapa.Keys)
    )
    && (esq != null && dir != null ==> esq.Repr !! dir.Repr)
    && Mapa == Uniao(Uniao(map[chave := valor], esq), dir)
  }

  constructor (chave:int, valor:T)
    ensures Valid() && fresh(Repr)
    ensures Mapa == map[chave := valor]

  function Buscar(chave:int):Option<T>
    requires Valid()
    reads Repr
    ensures chave in Mapa.Keys ==> Buscar(chave) == Some(Mapa[chave])
    ensures chave !in Mapa.Keys ==> Buscar(chave) == None

  method Adicionar(chave:int, valor:T)
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures Mapa == old(Mapa)[chave := valor]

}

class ArvoreBinariaBusca<T>
{
  //Abstração
  ghost var Mapa:map<int,T>
  ghost var Repr:set<object>
  //Implementação
  var raiz:Nodo?<T>

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {
    && this in Repr
    && (|Mapa.Keys| == 0 ==> raiz == null)
    && (|Mapa.Keys| != 0 ==>
      && raiz in Repr
      && raiz.Repr <= Repr
      && this !in raiz.Repr
      && raiz.Valid()
      && raiz.Mapa == Mapa
    )
  }
    
  constructor ()
    ensures Valid() && fresh(Repr)
    ensures Mapa == map[]
    
  function Buscar(chave:int):Option<T>
    requires Valid()
    reads Repr
    ensures chave in Mapa.Keys ==> Buscar(chave) == Some(Mapa[chave])
    ensures chave !in Mapa.Keys ==> Buscar(chave) == None
    
  method Adicionar(chave:int, valor:T)
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures Mapa == old(Mapa)[chave := valor]
}