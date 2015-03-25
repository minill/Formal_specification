class User 
{                                 //TOKENEER - SOROUSH & BEHROZ
	var	fingerprint:	int;
	var	validUser:	bool;
	var	token:	int;
	var	clearLevel:	int;
	var	wrong:	int;

	method	Init(tokenNumber:int, f:int, cl:int)
	modifies this;
	requires 1 == cl  || cl == 3;
	ensures token == tokenNumber;
	ensures fingerprint == f;	
	ensures clearLevel == cl;
	ensures validUser == true;
	ensures wrong == 0;
	{
		token := tokenNumber;
		fingerprint := f;
		clearLevel := cl;
		validUser := true;
		wrong := 0;
	}
	
	method	invalidUserToken()
	modifies this`validUser;
	ensures validUser == false;
	//requires that the method authentication must have been runned before this??
	{
		validUser := false;
	} 
	
}

class IdStation
{
	var	receivedToken:	User;
	var doorHighLevel: bool;
	var	doorLowLevel:	bool;
	var	accepted:	bool;
	
	predicate ready()
	reads this;
	{
		receivedToken == null
		&& accepted==false
		&& doorHighLevel == false 
		&& doorLowLevel == false		

	}

	predicate close()
	reads this;
	{
		accepted==false
		&& doorHighLevel == false 
		&& doorLowLevel == false
	}
	
	method Init()
	modifies this;
	ensures ready();
	{
		receivedToken := null;
	    accepted := false;
		doorHighLevel := false; 
		doorLowLevel := false;

	}	
	
	method ReceivedToken(u:User) 
	modifies this`receivedToken;
	requires u != null && u.validUser == true;
	requires this.ready();
	ensures receivedToken == u;
	{
		receivedToken := u; 
	}
	
	
	method Authentication(token:int, fp:int, clearLevelOnDoor:int)
	modifies this.receivedToken`wrong, this.receivedToken`validUser, `accepted, `doorHighLevel, `doorLowLevel;	
    requires close();
	requires receivedToken != null;
	requires receivedToken.wrong >= 0;
	requires receivedToken.validUser == true;
	ensures receivedToken != null;
	ensures receivedToken.wrong >= 0;

	ensures receivedToken == old(receivedToken);
	
	ensures	 receivedToken.fingerprint == fp &&
			 receivedToken.token == token &&
		     receivedToken.clearLevel == clearLevelOnDoor  &&
			 clearLevelOnDoor == 3 ==> accepted == true && 
			 doorHighLevel == true &&
			 doorLowLevel == false &&
			 receivedToken.validUser == old(receivedToken.validUser) &&
			 receivedToken.wrong == old(receivedToken.wrong);

	ensures receivedToken.fingerprint == fp &&
			 receivedToken.token == token &&
		     receivedToken.clearLevel == clearLevelOnDoor &&
			 clearLevelOnDoor == 1 ==> accepted == true && 
			 doorLowLevel == true &&
			 doorHighLevel == false &&
			 receivedToken.validUser == old(receivedToken.validUser) &&
			 receivedToken.wrong == old(receivedToken.wrong);
	
	ensures receivedToken.fingerprint == fp &&
			 receivedToken.token == token &&
		     receivedToken.clearLevel == clearLevelOnDoor &&
			 (clearLevelOnDoor != 1 && clearLevelOnDoor != 3) ==> close() &&
			 receivedToken.validUser == old(receivedToken.validUser) ;

	ensures receivedToken.fingerprint != fp ==> !accepted;

	ensures  receivedToken.token == token &&
		     receivedToken.clearLevel == clearLevelOnDoor &&
			 receivedToken.fingerprint != fp  && 
			 old(receivedToken.wrong) < 2 ==> accepted == false &&
			 receivedToken.wrong == old(receivedToken.wrong) + 1 &&
			 close() &&
			 receivedToken.validUser == true; 
			 
	ensures  receivedToken.token == token &&
		     receivedToken.clearLevel == clearLevelOnDoor &&
			 receivedToken.fingerprint != fp  && 
			 !(old(receivedToken.wrong) < 2) ==> (accepted == false &&
			 receivedToken.validUser == false) &&
			 close();

   ensures	!(receivedToken.token == token &&
		    receivedToken.clearLevel == clearLevelOnDoor) ==> accepted == false &&
			 receivedToken.validUser == false &&
			 close();

	{
		if(receivedToken.token == token &&
		   receivedToken.clearLevel == clearLevelOnDoor){
				if(receivedToken.fingerprint == fp)
				{
			
					if(clearLevelOnDoor == 3){
						accepted := true;	
						doorHighLevel := true;
					}
					else if(clearLevelOnDoor == 1){
						accepted:=true;
						doorLowLevel := true;
					} 
					else{
						accepted := false;
						doorHighLevel := false;
						doorLowLevel := false;
						receivedToken.wrong := receivedToken.wrong + 1 ;
					}
				}
				else // != fp
				{
						if(receivedToken.wrong < 2){
							accepted := false;
							receivedToken.wrong := receivedToken.wrong + 1; 
						}
						else{
							accepted := false;
							receivedToken.invalidUserToken();
						}
				}
		}
		else{	//token invalid.
			accepted := false;
			receivedToken.invalidUserToken();

		}
		
	}	
}

method	Main()
	{
	
		var	userCase1 := new User;
		var	userCase2 := new User;
		var	userCase3 := new User;
		var	userCase4 := new User;
		var idStation := new IdStation;
		
		//CASE 1 - DENIED AUTHENTICATION, WRONG FINGERPRINT
		userCase1.	Init(1234, 4321, 3);
		idStation.Init();
		idStation.ReceivedToken(userCase1);
		assert userCase1.wrong == 0;
		assert idStation.receivedToken == userCase1;
		idStation.Authentication(1234,1122, 3);
		assert idStation.receivedToken == userCase1;
		assert idStation.accepted == false;
		assert userCase1.wrong == 1;
		idStation.Authentication(1234,1202, 3);
		assert userCase1.wrong == 2;
		idStation.Authentication(1234,4321, 3);
		assert userCase1.wrong == 2;
		assert idStation.doorHighLevel == true;
		assert idStation.doorLowLevel == false;
		
		//CASE 2 - DENIED AUTHENTICATION, WRONG CLEARENCE-LEVEL
		userCase2.Init(2345, 5432, 1);
	    idStation.Init();
		idStation.ReceivedToken(userCase2);
		assert userCase2.wrong == 0;
		assert idStation.receivedToken == userCase2;
		idStation.Authentication(2345,5432, 3);
		assert idStation.receivedToken == userCase2;
		assert idStation.accepted == false;
		assert userCase2.validUser == false;
		
		//CASE 3 - DENIED AUTHENTICATION, WRONG TOKEN-NUMBER
		userCase3.Init(3456, 4321, 3);
		idStation.Init();
		idStation.ReceivedToken(userCase3);
		assert userCase3.wrong == 0;
		idStation.Authentication(1134,4321, 3);
		assert idStation.accepted == false;
		assert userCase3.validUser == false;
		
		//CASE 4 - ACCEPTED AUTHENTICATION
		userCase4.Init(1234, 4321, 3);
		idStation.Init();
		idStation.ReceivedToken(userCase4);
		assert userCase4.wrong == 0;
		idStation.Authentication(1234,4321, 3);
		assert idStation.accepted == true;
		
		
		
		
		
		
	}