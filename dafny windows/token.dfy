datatype ClearanceLevel = LOW | MEDIUM | HIGH

class Token {

    var valifyer : bool;
	var clearance_level : ClearanceLevel;
	var user_ID	: nat;
	


method INIT (id : nat, sec_lvl : ClearanceLevel)
modifies this`valifyer
modifies this`user_ID
modifies this`clearance_level
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


class User{
	var token 		: Token

	method INIT(cl : ClearanceLevel)
	
	modifies this`token
	ensures token == null	
	{
		token := null;
		
	}


	}


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

method register(user : User, cl : ClearanceLevel)
	modifies this`userSet
	modifies this`idCounter
	modifies user`token, user.token
		requires user != null
		requires 	Valid_Enrollment()
		requires (cl == LOW) || (cl == MEDIUM) ||(cl == HIGH)
		ensures 	Valid_Enrollment()
		ensures old(idCounter)  == idCounter - 1 
		{

			userSet := userSet + {idCounter};
			user.token  := new Token.INIT(idCounter, cl);
			idCounter := idCounter + 1;

		}




}


//================================= Class ID STATION  ===========================================

/**
There are three different types of ID one that validate to HIGH security, one to MEDIUM, one for LOW. It's decided in the 

**/

class IDStation{
var authication_level : ClearanceLevel
predicate activeIDStation()
reads this`authication_level
{
	(authication_level == LOW) || (authication_level == MEDIUM) ||(authication_level == HIGH)
}

method INIT(auth_level : ClearanceLevel)
	
	modifies this`authication_level
		ensures authication_level == auth_level
		ensures activeIDStation()
			{
	authication_level := auth_level;
}



/**
 returns a bool that is connected to the supersystem, 


 NOTE TO SUPERVISOR  : : token == null returns false, invalidate token. I wanted this to happend, but did not 
																		know how , so had to require nonNull

 if isValid == true: user will be granted permission to enter the system
			== false users token will be invalidated, alarm will sound and the doors too system will be shut.


The input value of auth_level, will set the classes current level to that level via setClearanceLevel
			CONDITIONS:

requires: a Natural number as ID
requires: a valid autication level
requires a nonnull token

ensures	: if userID != token.userID,					return false, invalidate token
		: token.clearanceLevel =!	auth_level			returns false, invaldatetoken
		:												auth_level == this.authicationLevel

**/
method openDoor(userID : nat, token : Token) returns (isAuthenticated : bool)
	modifies this`authication_level
	
    requires token != null
		requires userID >= 0
		ensures		(userID == token.user_ID) &&	(authication_level == token.clearance_level)  <==> isAuthenticated
{	

	  isAuthenticated := (userID == token.user_ID) && authication_level == token.clearance_level;
  return isAuthenticated;
  }

}




class TokeneerSystem {

var doorOpen : bool;
var alarmRing : bool;
var idSt : IDStation;
var enrollst: EnrollmentStation;
var user : User


predicate Valid()
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

method INIT(cl : ClearanceLevel) 
	modifies this`doorOpen
	modifies this`alarmRing
	modifies this.idSt	
	modifies this`idSt
	modifies this.enrollst
	modifies this`enrollst
	

		requires (cl == LOW) || (cl == MEDIUM) ||(cl == HIGH)
		ensures Applicable()
		ensures Valid()

{
	doorOpen := false;
	alarmRing := false;
	idSt := new IDStation.INIT(cl);
	enrollst := new EnrollmentStation.INIT();

}


/**
a user enrolls: it's token must either be null or not have a valid token

**/

method enroll (u : User, cl : ClearanceLevel)
modifies this.enrollst, this.enrollst`idCounter
modifies u.token
modifies u`token
modifies this`enrollst

	requires u != null
	requires u.token == null
	requires  (cl == LOW) || (cl == MEDIUM) ||(cl == HIGH)
	requires Valid();

	ensures Valid()
	ensures old(doorOpen) == doorOpen && old (alarmRing) == alarmRing
{
	enrollst.register(u,cl);
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
modifies t`user_ID

	requires Valid()
	requires id >= 0
	requires t != null
	requires t.valifyer
	requires idSt != null
	requires (idSt.authication_level == LOW) ||  (idSt.authication_level == MEDIUM) || (idSt.authication_level == HIGH)
	
		
		ensures Valid()
		ensures (t.user_ID == id  && t.clearance_level == idSt.authication_level) ==> (!alarmRing && doorOpen)
		ensures (t.user_ID != id || t.clearance_level != idSt.authication_level) <==> !doorOpen && !t.valifyer && alarmRing
{
		
		//wanted to use method idStn.openDoor, but seems like that cant be done in dafny....
		if (t.user_ID == id  && t.clearance_level == idSt.authication_level){

		alarmRing := false;
		doorOpen := true;

		}else {
		alarmRing := true;
		doorOpen := false;
		t.invalidateToken();
		
		}
}


}

























