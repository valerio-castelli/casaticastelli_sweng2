open util/integer as integer

sig float{}

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

fact{
	// No locations should simultaneously belong to two different zones
	all loc: Location | (no disj z1, z2:Zone | (loc in z1.boundaries && loc in z2.boundaries))
	// Two locations cannot be identical
	no disj loc1,loc2: Location | (loc1.latitude = loc2.latitude && loc1.longitude = loc2.longitude)
}

fact{
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


sig Taxi{
	taxiCode: Int,
	licensePlate: String, 
	taxiStatus: TaxiStatus,
	serves: lone Request
}{
	taxiCode>=0
}
fact{
	// If a taxi is available, there should be no request associated
	all t:Taxi|	t.taxiStatus = available implies (t.serves = none)
	// If a taxi is currently on a ride, there should be a request which is currently served
	all t:Taxi| t.taxiStatus = currentlyRiding implies (one r:Request | r in t.serves)
}

sig TaxiDriver{
	name: String,
	surname: String,
	taxiLicense: String,
	drivingLicense: String,
	mobilePhoneNumber: String,
	drives: Taxi
}

sig Zone{
	zoneId: Int,
 	contains: set Taxi,
	boundaries: some Location
}
{
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
	instance: TaxiManager
}

sig DBManager{
	instance: DBManager
}

sig NotificationManager{
	instance: NotificationManager
}

sig ZoneManager{
	instance: ZoneManager
}

fact{
	// Singletons
	#AccessManager=1
	#SettingsManager=1
	#TaxiManager=1
	#DBManager=1
	#NotificationManager=1
	#ZoneManager=1
}

abstract sig User{
	userId: Int,
	name: String,
	surname: String,
	mobilePhoneNumber: String
}{
	userId >= 0
}

sig Guest extends User{}

sig RegisteredUser extends User{
	username: String,
	password: String,
	usesAccessManager: AccessManager
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
	message: String
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





pred show{
}


run show for 3 but 5 Location, 5 Taxi
