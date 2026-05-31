#include <math.h>

// --- DÉFINITION DES BROCHES DE SORTIE ---
const int pinCh1 = 3;  // Sinusoïde 1 (Nécessite Filtre RC: 330 ohms + 100 nF)
const int pinCh2 = 6;  // Sinusoïde 2 (Nécessite Filtre RC: 330 ohms + 100 nF)
const int pinCh3 = 9;  // Carré 1 (Nécessite Pont diviseur: 1 kOhm / 2 kOhm)
const int pinCh4 = 11; // Carré 2 (Nécessite Pont diviseur: 1 kOhm / 2 kOhm)

// --- VARIABLES DES SIGNAUX ---
float phase1 = 0, phase2 = 0, phase3 = 0, phase4 = 0;
float f1 = 1000, f2 = 1000, f3 = 1000, f4 = 1000;
float amp1 = 1.0, amp2 = 1.0;

// --- GESTION DU TEMPS ---
unsigned long lastSignalTime = 0;
unsigned long lastPotTime = 0;

// --- VARIABLES POUR L'ALGORITHME SIGMA-DELTA (SINE) ---
int sigma1 = 0, out1 = 0;
int sigma2 = 0, out2 = 0;

void setup() {
  // Configuration des broches en sortie
  pinMode(pinCh1, OUTPUT);
  pinMode(pinCh2, OUTPUT);
  pinMode(pinCh3, OUTPUT);
  pinMode(pinCh4, OUTPUT);
}

void loop() {
  unsigned long currentTime = micros();

  // ----------------------------------------------------
  // 1. LECTURE DES 6 POTENTIOMÈTRES (Toutes les 40 ms)
  // ----------------------------------------------------
  if (currentTime - lastPotTime >= 40000) {
    lastPotTime = currentTime;

    // A0 à A3 : Contrôle des Fréquences de 1000 Hz à 3000 Hz
    f1 = map(analogRead(A0), 0, 1023, 1000, 3000);
    f2 = map(analogRead(A1), 0, 1023, 1000, 3000);
    f3 = map(analogRead(A2), 0, 1023, 1000, 3000);
    f4 = map(analogRead(A3), 0, 1023, 1000, 3000);

    // A4 et A5 : Contrôle des Amplitudes (Canal 1 et 2)
    // Résultat entre 0.0 et 1.0
    amp1 = analogRead(A4) / 1023.0;
    amp2 = analogRead(A5) / 1023.0;
  }

  // ----------------------------------------------------
  // 2. GÉNÉRATION DES SIGNAUX (Toutes les 20 µs = 50 kHz)
  // ----------------------------------------------------
  if (currentTime - lastSignalTime >= 20) {
    // Calcul précis du temps écoulé (dt)
    float dt = (currentTime - lastSignalTime) / 1000000.0;
    lastSignalTime = currentTime;

    // Calcul de l'avancement de la phase pour chaque onde
    phase1 += 2.0 * M_PI * f1 * dt; if (phase1 >= 2.0 * M_PI) phase1 -= 2.0 * M_PI;
    phase2 += 2.0 * M_PI * f2 * dt; if (phase2 >= 2.0 * M_PI) phase2 -= 2.0 * M_PI;
    phase3 += 2.0 * M_PI * f3 * dt; if (phase3 >= 2.0 * M_PI) phase3 -= 2.0 * M_PI;
    phase4 += 2.0 * M_PI * f4 * dt; if (phase4 >= 2.0 * M_PI) phase4 -= 2.0 * M_PI;

    // --- GÉNÉRATION CH1 : SINUSOÏDE 1 ---
    // Bridage logiciel : multiplier par 84 au lieu de 127.5 pour plafonner à 3.3V
    int target1 = (int)((sin(phase1) + 1.0) * 84.0 * amp1); 
    sigma1 += target1 - out1;
    if (sigma1 >= 0) { digitalWrite(pinCh1, HIGH); out1 = 255; } 
    else             { digitalWrite(pinCh1, LOW);  out1 = 0;   }

    // --- GÉNÉRATION CH2 : SINUSOÏDE 2 ---
    // Bridage logiciel à 3.3V avec ajustement de l'amplitude
    int target2 = (int)((sin(phase2) + 1.0) * 84.0 * amp2); 
    sigma2 += target2 - out2;
    if (sigma2 >= 0) { digitalWrite(pinCh2, HIGH); out2 = 255; } 
    else             { digitalWrite(pinCh2, LOW);  out2 = 0;   }
    
    // --- GÉNÉRATION CH3 ET CH4 : SIGNAUX CARRÉS ---
    digitalWrite(pinCh3, (phase3 < M_PI) ? HIGH : LOW);
    digitalWrite(pinCh4, (phase4 < M_PI) ? HIGH : LOW);
  }
}