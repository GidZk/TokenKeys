class Sorted {


//------------- 1a -------------

//solution 1

predicate Sorted( a: seq<int>)
	requires a != null;

reads a;
{
 forall i : int :: 0 <= i < a.Length-1 ==> a[i] < a[i+1]
}



// ------------- 1b -------------

// solution 2

predicate Sorted2(a : seq<int>)
	requires a != null;

reads a;
{

forall i , j : int :: 0 <= i < j < a.Length ==> a[i]< a[j]

}



// -------------   2a   -------------
/*
ghost method Sortedlol(a : seq<int>)
	requires a != null;
	requires a.Length >= 2;

  ensures Sorted(a) ==> Sorted2(a)
{
}
*/
ghost method Sortedlol2(a : seq<int>)

	requires a != null;
	requires  a.Length >= 2;
  	ensures Sorted2(a) ==> Sorted(a)
{
}


// -------------   2b   ------------- PAPER


// -------------   3a   -------------

/*

With multiset we get that the sequence [cow, horse, cow, horse] is equivalent to
the sequence [horse , cow, horse, cow].

the sequence and repetitions of the sequence does not matter, it is just the 
elements that are in the multiset.


So what p checks is if the number of different animals in multiset a is 
the same as in multiset b





FOR 3B, THINK ABOUT BUTTERFLIES EXISTS IN B IN A, EXISTS PREDICATE ETC 
*/







}