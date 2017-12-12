
class Token {




    var valifyer : bool;
	var clearance_level : nat;
	var user_ID	: nat;
	
	

method INIT (id : nat, sec_lvl : nat)
modifies this`valifyer
modifies this`user_ID
modifies this`clearance_level
requires 1 <= sec_lvl <= 3
ensures 		valifyer 
			&&  user_ID == id 
			&&  clearance_level == sec_lvl
{
clearance_level := sec_lvl;
user_ID := id;
valifyer := true;
}



/*
requires : that this current token already is valid
ensures  : that the current token is invalid
*/



method invalidateToken()
modifies this`valifyer
requires  valifyer
ensures  !valifyer 

{
valifyer := false;
}

}


//================================= Class User  ===========================================
/*

class User{
	var token 		: Token

	method INIT(cl : ClearanceLevel)
	
	modifies this`token
	ensures token == null	
	{
		token := null;
		
	}


	}

	*/
//================================= Class Enrolmmentsys  ===========================================


class EnrollmentStation{

var idCounter : nat;
var userSet : set<nat>;

predicate Valid_Enrollment()
reads this`idCounter
reads this`userSet
{
	 0 <= idCounter 
}


method INIT()
	modifies this`idCounter
	modifies this`userSet
		ensures userSet == {} && |userSet| == 0 
		ensures idCounter == 0
  {
    userSet := {};
    idCounter := 0;
  }

method register(cl : nat) returns (token : Token)
	modifies this`userSet
	modifies this`idCounter
		
		requires 	Valid_Enrollment()
		requires  1 <= cl <= 3
		ensures 	Valid_Enrollment()
		ensures old(idCounter) in userSet
		ensures old(idCounter)  == idCounter - 1 
		{

			userSet := userSet + {idCounter};
			token  := new Token.INIT(idCounter, cl);
			idCounter := idCounter + 1;

		}




}


//================================= Class ID STATION  ===========================================

/**
There are three different types of ID one that validate to HIGH security, one to MEDIUM, one for LOW. It's decided in the 

**/

class IDStation{
var authication_level : nat

method INIT(auth_level : nat)
	
	modifies this`authication_level
		requires  1 <= auth_level <= 3
		ensures authication_level == auth_level
			{
	authication_level := auth_level;
}



/**
 returns a bool that is connected to the supersystem, 

 NOTE TO SUPERVISOR  : if the input token is null, then I wanted to invalidate the token, but I could not make it compile at all.
 so instead I chose to change the design of the method to: e to require a non-null token from the user;
 that is that the user ALREADY has enrolled to the system and recieved a valid token with a ID number

 if isValid == true: user will be granted permission to enter the system
			== false users token will be invalidated, alarm will sound and the doors too system will be shut.


The input value of auth_level, will set the classes current level to that level via setClearanceLevel
			CONDITIONS:

				requires: a Natural number as ID
				requires: a valid autication level
				requires a nonnull token

				ensures	: if userID != token.userID or token.clearanceLevel <=	auth_level					return false, invalidate token
		:						returns false, invaldatetoken
		:				token.clearanceLevel >=	auth_level													return true

**/
method openDoor(userID : nat, token : Token) returns (isAuthenticated : bool)
	modifies this`authication_level
	requires 1<= authication_level <=3
    requires token != null
		requires userID >= 0
		ensures		(userID == token.user_ID) &&(token.clearance_level  >= authication_level )  <==> isAuthenticated
{	

	  isAuthenticated := (userID == token.user_ID) && token.clearance_level  >= authication_level ;
  return isAuthenticated;
  }

}




class TokeneerSystem {

var doorOpen : bool;
var alarmRing : bool;
var idSt : IDStation;
var enrollst: EnrollmentStation;

predicate StationsRunning()
	reads this.idSt;
	reads this`idSt;
	reads this.enrollst
	reads this`enrollst;
	
	{
	 idSt != null && enrollst != null 
	}

// tells us that the user can enroll and or apply for ID.
predicate Applicable()
	reads this`doorOpen;
	reads this`alarmRing;
{
		!doorOpen && !alarmRing
	}

/*
construct a fresh TokeneerSystem that 
*/

method INIT(cl : nat) 
	modifies this`doorOpen
	modifies this`alarmRing
	modifies this.idSt	
	modifies this`idSt
	modifies this.enrollst
	modifies this`enrollst
	

		requires 1 <= cl <= 3
		ensures Applicable()
		ensures StationsRunning()

{
	doorOpen := false;
	alarmRing := false;
	idSt := new IDStation.INIT(cl);
	enrollst := new EnrollmentStation.INIT();

}


/**
a user enrolls: it's token must either be null or not have a valid token

**/

method enroll ( cl : nat) returns (token : Token)
modifies this.enrollst, this.enrollst`idCounter
modifies this`enrollst

	requires 1 <= cl <= 3
	requires StationsRunning();

	ensures StationsRunning()
	ensures old(doorOpen) == doorOpen && old (alarmRing) == alarmRing
{
	token := enrollst.register(cl);
}

/*
Checks that users token and opens the door if both userID and tokenID is the same, ASWELL as the current clearance level as the ID station.

	requires a user that holds a token (that has enrolled) and is valid
	and the comoponents of the system to be initaited

	CONDITIONS 
	-----------
	ensures :	inputID == tokenID  
				AND 
				usersClearanceLevel	== enrollment then  :  openDoor = true , alarmRing = false

				no alarm, and the door is open for the user


				-------------
	ensures:	inputID != tokenID
				OR	
				userClearanceLevel != enrollmentc			thne openDoor = false, alarmRing = true
				door closes, alarm goes off


*/
method validateUser (id : nat, t : Token)
modifies this`alarmRing
modifies this`doorOpen
modifies this.idSt, this`idSt
modifies t
modifies t`valifyer

	requires StationsRunning()
	requires 1 <= id <= 3
	requires t != null
	requires t.valifyer
	requires idSt != null
	requires 1 >= idSt.authication_level >= 3 	// setting the range for ClearanceLevel
		
		ensures StationsRunning()
		ensures (old(t.user_ID) == id  && old(t.clearance_level) >= idSt.authication_level) ==> (!alarmRing && doorOpen)
		ensures (old(t.user_ID) != id || old(t.clearance_level) <= old(idSt.authication_level)) <==> !doorOpen && !t.valifyer && alarmRing
{
		
		//wanted to use method idStn.openDoor, but seems like that cant be done in dafny....
		if (t.user_ID == id  && t.clearance_level >= idSt.authication_level){

		alarmRing := false;
		doorOpen := true;

		}else {
		alarmRing := true;
		doorOpen := false;
		t.invalidateToken();
		
		}
}



}







class test{

method Main(){

var system := new TokeneerSystem.INIT(2);



}



}








