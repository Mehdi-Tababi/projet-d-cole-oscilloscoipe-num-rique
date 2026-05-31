const int pin1 = 34; const int pin2 = 35;
const int pin3 = 32; const int pin4 = 33;

unsigned long lastSampleTime = 0;
// Prise de mesure toutes les 250 microsecondes (Fréquence d'échantillonnage de 4000 Hz)
const unsigned long SAMPLE_INTERVAL_US = 100; 

void setup() {
  // ATTENTION : Vitesse très élevée indispensable !
  Serial.begin(921600);
  analogReadResolution(12);
}

void loop() {
  unsigned long currentTime = micros();

  if (currentTime - lastSampleTime >= SAMPLE_INTERVAL_US) {
    lastSampleTime = currentTime;

    int val1 = analogRead(pin1);
    int val2 = analogRead(pin2);
    int val3 = analogRead(pin3);
    int val4 = analogRead(pin4);

    // Format optimisé pour envoyer les données le plus vite possible
    Serial.printf("%d,%d,%d,%d\n", val1, val2, val3, val4);
  }
}