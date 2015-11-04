open util/integer as integer

/* Signatures */
sig float{}
sig string{}

sig Location{
	latitude: float,
	longitude: float
}

sig LocationUpdate{
	relativeTo: Location,
	sentBy: Taxi,
	sentTo: TaxiManager
}{
}

sig Taxi{
	taxiCode: Int,
	licensePlate: string, 
	taxiStatus: TaxiStatus,
	serves: lone Request,
	isManagedBy: TaxiManager
}{
	taxiCode>=0
}

sig TaxiDriver{
	name: string,
	surname: string,
	taxiLicense: string,
	drivingLicense: string,
	mobilePhoneNumber: string, 
	drives: Taxi,
	isNotifiedBy: TaxiManager
}

sig Zone{
	zoneId: Int,
 	contains: set Taxi,
	boundaries: some Location
}
{	
	// Each zone must contain at least 3 points in order to have a proper boundary
	#boundaries >= 3
	zoneId >= 0
}

enum TaxiStatus{
	available,
	unavailable,
	currentlyRiding,
	outsideCity
}

sig AccessManager{
	instance: AccessManager
}

sig SettingsManager{
	instance: SettingsManager
}

sig TaxiManager{
	instance: TaxiManager,
	handles: set Reservation,
	manages: set Request,
	unavailableTaxis: set Taxi,
	availableTaxis: set Taxi,
	currentlyRidingTaxis: set Taxi,
	outsideCityTaxis: set Taxi
}

sig DBManager{
	instance: DBManager
}

sig NotificationManager{
	instance: NotificationManager,
	isUsedBy: TaxiManager,
	sends: set Notification
}

sig ZoneManager{
	instance: ZoneManager,
	isUsedBy: TaxiManager,
	manages: set Zone
}

abstract sig User{
	userId: Int,
	name: string,
	surname: string,
	mobilePhoneNumber: string
}{
	userId >= 0
}

sig Guest extends User{}

sig RegisteredUser extends User{
	username: string,
	password: string,
	usesAccessManager: AccessManager,
	usesSettingsManager: SettingsManager
}

sig Request{
	requestId: Int,
	location: Location,
	sentBy: User
}{
	requestId >= 0
}

sig Reservation{
	reservationId: Int,
	origin: one Location,
	destination: one Location,
	madeBy: RegisteredUser
}{
	reservationId >= 0
}

abstract sig Notification{
	notificationId: Int,
	message: string
}{
	notificationId >= 0
}

sig IncomingTaxiNotification extends Notification{
	ETA: Int,
	taxiCode: Int,
	secretCode: Int
}{
	ETA >= 0
	taxiCode >= 0
	secretCode >= 0
	// The taxi code must belong to a real taxi 
	one t1:Taxi | taxiCode=t1.taxiCode
}

sig ReservationConfirmationNotification extends Notification{
}

sig NoTaxiAvailableNotification extends Notification{
}

sig TaxiSecretCodeNotification extends Notification{
	secretCode: Int
}{
	secretCode >= 0
}

/* Facts */

fact AllNotificationInNotificationManager{
	// All notifications are sent by the notification manager
	all n: Notification | one nm: NotificationManager | n in nm.sends
}

fact AllZonesAreManagedByZoneManager{
	// All zones are actually managed
	all z: Zone | one zm: ZoneManager | z in zm.manages
}


fact AllTaxisAreDrivenByASingleDriver{
	// All taxis are driven by exactly a driver
	all t: Taxi | one td: TaxiDriver | t in td.drives
}

fact TaxiStatusCoherence{
	all t:Taxi | t.taxiStatus = available <=> (one tm: TaxiManager | t in tm.availableTaxis)
	all t:Taxi | t.taxiStatus = unavailable <=> (one tm: TaxiManager | t in tm.unavailableTaxis)
	all t:Taxi | t.taxiStatus = currentlyRiding <=> (one tm: TaxiManager | t in tm.currentlyRidingTaxis)
	all t:Taxi | t.taxiStatus = outsideCity <=> (one tm: TaxiManager | t in tm.outsideCityTaxis)
}


fact TaxiStatusCorrectlyUpdated {
	// If a taxi is available, there should be no request associated
	all t:Taxi|	t.taxiStatus = available implies (t.serves = none)
	// If a taxi is currently on a ride, there should be a request which is currently served
	all t:Taxi| t.taxiStatus = currentlyRiding implies (one r:Request | r in t.serves)
	// If a taxi is outside the city, it cannot be associated with requests
	all t:Taxi| t.taxiStatus = outsideCity implies (t.serves = none)
	// If a taxis is unavailable, it cannot be associated with requests
	all t:Taxi| t.taxiStatus = unavailable implies (t.serves = none)
}

fact NoLocationInTwoZones{
	// No locations should simultaneously belong to two different zones
	all loc: Location | (no disj z1, z2:Zone | (loc in z1.boundaries && loc in z2.boundaries))
}

fact NoTwoIdenticalLocations{
	// Two locations cannot be identical
	no disj loc1,loc2: Location | (loc1.latitude = loc2.latitude && loc1.longitude = loc2.longitude)
}

fact UniquenessOfIdentifiers{
	// Uniqueness of identifiers
	// Two zones cannot have an identical zoneId
	no disj z1,z2: Zone | (z1.zoneId = z2.zoneId)
	// Two taxis cannot have the same taxi code, license plate
	no disj t1,t2: Taxi | (t1.taxiCode = t2.taxiCode || t1.licensePlate = t2.licensePlate)
	// Two users cannot have the same userId
	no disj u1,u2 :User | (u1.userId = u2.userId)
	// Two registered users cannot have the same username
	no disj u1,u2: RegisteredUser | (u1.username = u2.username) 
	// Two requests cannot have the same identifier
	no disj r1,r2: Request | (r1.requestId = r2.requestId)
	// Two reservations cannot have the same identifier
	no disj r1,r2: Reservation | (r1.reservationId = r2.reservationId)
	// Two taxi drivers cannot have the same taxi license or driving license or phone number
	no disj td1,td2:TaxiDriver | (td1.taxiLicense = td2.taxiLicense || td1.drivingLicense = td2.drivingLicense || td1.mobilePhoneNumber = td2.mobilePhoneNumber) 
}

fact SingletonClasses{
	// Singletons
	#AccessManager=1
	#SettingsManager=1
	#TaxiManager=1
	#DBManager=1
	#NotificationManager=1
	#ZoneManager=1
}

/* Predicates */
pred associateRequestToTaxi(t, t':Taxi, r: Request){
	// precondition
	t.taxiStatus = available
	#t.serves = 0
	// postcondition
	t'.taxiStatus = currentlyRiding
	r in t'.serves
	t'.isManagedBy = t.isManagedBy
}

pred show{
	#Taxi = 1
	#Zone = 1
	#Notification = 0
	#User = 2
}


run associateRequestToTaxi


