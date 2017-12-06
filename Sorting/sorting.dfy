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
method SortedGhost(a : seq<int>)
	requires a != null;
	requires a.Length >= 2;

  ensures Sorted(a) ==> Sorted2(a)
{
}
*/

 method Sortedlghost2(a : seq<int>)

	requires a != null;
	requires  a.Length >= 2;
  	ensures Sorted2(a) ==> Sorted(a)
{

}


// -------------   2b   ------PAPER


// -------------   3a   -------------
/*

With multiset we get that the sequence [cow, horse, cow, horse] is equivalent to
the sequence [horse , cow, horse, cow].

the sequence and repetitions of the sequence does not matter, it is just the 
elements that are in the multiset and the occuances of it.


So what p checks is if the number of different animals in multiset a is 
the same as in multiset b
*/

predicate p(a :seq<int> , b : seq<int>)
{
|a| == |b| && forall i : int :: 0 <= i < a.Length ==>  helper(a,a[i],0) == helper(b,b[i],0)
}

function helper (s : seq<int>,value : int, counter : int) : int{

if (s == []) then counter 
else if (s[0] == value) then helper(s[1..],value,counter+1) 
else  helper(s[1..],value,counter)

}

//---------------- 4a ----------------------

method sortme(src : arr<int>) 
requires src != null
ensures 	p(t[..]) &&
			(old(src) == src)   // sorted in place, ref to array should be the same
{   }


//----------------- 4b ---------------------

/*
It's a bit unclear what you want from us, do you want a method or 
*/




















}