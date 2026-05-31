/**
 * ╔══════════════════════════════════════════════════════════════════════════╗
 * ║       OSCILLOSCOPE EPT — SÉRIE TEKLAB 4000  (v8.0 PRO)                 ║
 * ║       Interface Professionnelle — 4 Canaux Différentiels                ║
 * ║  v8.0 — Simulation précision Arduino IDE :                              ║
 * ║   • Port série 921600 bps — ~3000 samples/sec réels                    ║
 * ║   • SAMPLE_RATE auto-mesurée en temps réel (Hz affiché)                ║
 * ║   • Parser série robuste : trame partielle, CRC, anti-glitch            ║
 * ║   • Buffer série interne 4096 octets (zéro perte à haut débit)         ║
 * ║   • Mode démo cadencé millis() identique au vrai port                  ║
 * ║   • Logo EPT chargé depuis EPT_logo.gif (fallback vectoriel auto)      ║
 * ║   • Knobs : AMP / ZOOM / TEMPS                                          ║
 * ║   • FFT Cooley-Tukey radix-2 O(N·logN) — 10× plus rapide               ║
 * ║   • Buffer circulaire natif O(1) — plus de System.arraycopy()          ║
 * ║   • Fenêtre Hann pré-calculée + coeffs Butterworth mis en cache        ║
 * ║   • Plein écran (F) + Thème clair/sombre (T)                           ║
 * ╚══════════════════════════════════════════════════════════════════════════╝
 *
 * Dépendances : controlP5 (lib Processing)
 * Port série  : COM8 @ 921600 bps — CSV : "v1,v2,v3,v4\n"  (0-4095)
 * Raccourcis  : F=Fullscreen  T=Thème  Espace=RUN/STOP  R=ResetZoom  A=AutoScale
 */

import controlP5.*;
import processing.serial.*;
import java.util.Arrays;

// ═══════════════════════════════════════════════════════════════════════════
//  CONSTANTES
// ═══════════════════════════════════════════════════════════════════════════
final int   BASE_W        = 1440;
final int   BASE_H        = 900;
final int   SCREEN_X      = 10;
final int   SCREEN_Y      = 10;
final int   SCREEN_W      = 960;
final int   SCREEN_H      = 700;
final int   PANEL_X       = SCREEN_X + SCREEN_W + 18;
final int   PANEL_W_CST   = BASE_W - PANEL_X - 10;
final int   BUFFER_SIZE   = 8000;
// ─── Débit série 921600 bps ────────────────────────────────────────────────
// Trame "v1,v2,v3,v4\n" ≈ 28 octets → 921600/10 / 28 ≈ 3291 trames/sec
// On garde SAMPLE_RATE comme valeur de référence initiale, puis on la
// recalcule dynamiquement via la mesure réelle du débit port.
final int   BAUD_RATE     = 921600;
float       SAMPLE_RATE   = 3000.0;   // mis à jour dynamiquement (auto-mesure)
final float TENSION_BASE  = 0.275;
final int   NUM_CH        = 4;
final int   FFT_SIZE      = 1024;   // puissance de 2 pour FFT radix-2
final int   FFT_BINS      = FFT_SIZE/2;  // bins utiles (fréquences positives)

// ─── Buffer circulaire : head pointe sur la prochaine case à écrire
int[]  ringHead = {0, 0, 0, 0};    // remplace System.arraycopy()

// ─── Mesure débit réel (auto-calibration SAMPLE_RATE) ─────────────────────
long   rateCountSamples = 0;       // trames reçues depuis dernière mesure
long   rateLastMillis   = 0;       // timestamp dernière mesure
float  measuredSPS      = 0;       // samples/sec mesurés (affiché statut)
final  int RATE_WINDOW_MS = 500;   // fenêtre de mesure (ms)

// ─── Buffer interne série (protection trame partielle à haut débit) ────────
StringBuilder serialBuf = new StringBuilder(256);

// ─── Démo : cadencée sur millis() pour simuler exactement le vrai débit ───
long   demoLastMs = 0;
final  float DEMO_SPS = 3000.0;    // samples/sec injectés en démo

// Fenêtre Hann pré-calculée pour la FFT (calculée 1 seule fois)
float[] hannWindow = new float[FFT_SIZE];

// ═══════════════════════════════════════════════════════════════════════════
//  PALETTES
// ═══════════════════════════════════════════════════════════════════════════
boolean darkMode = true;
color C_APP_BG, C_CHASSIS, C_CHASSIS_LT, C_SCREEN_BG;
color C_GRID_FINE, C_GRID_MED, C_GRID_CENTER;
color C_PANEL_BG, C_PANEL_BORDER;
color C_TEXT_MAIN, C_TEXT_DIM, C_TEXT_ACCENT;
color C_BTN_RUN, C_BTN_STOP, C_BTN_WARN, C_BTN_BLUE, C_BTN_PURPLE;
color C_KNOB_RING, C_KNOB_CTR, C_BEZEL;

final color[] CH_COLORS = {
  color(255, 65, 55),
  color( 50,225, 75),
  color( 55,165,255),
  color(255,205, 35)
};

// ═══════════════════════════════════════════════════════════════════════════
//  OBJETS GRAPHIQUES
// ═══════════════════════════════════════════════════════════════════════════
ControlP5  cp5;
PGraphics  gScreen;   // écran CRT complet
PGraphics  gBezel;    // cadre pré-rendu
PGraphics  gGrid;     // grille pré-rendue
PGraphics  gLogo;     // logo EPT vectoriel pré-rendu
Serial     monPort;

// ═══════════════════════════════════════════════════════════════════════════
//  ÉTAT GLOBAL
// ═══════════════════════════════════════════════════════════════════════════
boolean showSplash   = true;
int     splashStart;
boolean powerOn      = true;
boolean runOscillo   = true;
boolean showFFT      = false;
boolean showCursors  = false;
boolean isFullscreen = false;
int     baseTemps    = 2;

float[]   gain    = {1, 1, 1, 1};
float[]   fzoom   = {1, 1, 1, 1};
float[]   posY    = {0, 0, 0, 0};
boolean[] inv     = {false,false,false,false};
boolean[] active  = {true, true, true, true};
boolean[] math    = {false,false,false,false};

float[][] rawHist = new float[NUM_CH][BUFFER_SIZE];

// ═══════════════════════════════════════════════════════════════════════════
//  FILTRES — CACHE + COEFFICIENTS PRÉ-CALCULÉS
// ═══════════════════════════════════════════════════════════════════════════
int[]   filterMode   = {0,0,0,0};
float[] filterCutoff = {0.1,0.1,0.1,0.1};
int[]   filterWindow = {5,5,5,5};

// Coefficients Butterworth pré-calculés [ch][b0,b1,b2,a1,a2]
float[][] bwCoeff = new float[NUM_CH][5];
float[]   bwFcLast= {-1,-1,-1,-1};  // fc lors du dernier calcul des coeffs

// États IIR (délais)
float[][] bwX1 = new float[NUM_CH][1];
float[][] bwX2 = new float[NUM_CH][1];
float[][] bwY1 = new float[NUM_CH][1];
float[][] bwY2 = new float[NUM_CH][1];

// Cache signal filtré [ch][pixel]
float[][] sigCache    = new float[NUM_CH][SCREEN_W];
boolean[] cacheValid  = {false,false,false,false};
long[]    lastSample  = new long[NUM_CH];  // timestamp dernier sample

// Paramètres qui invalidaient le cache
float[]   cachePosY   = {999,999,999,999};
float[]   cacheGain   = {999,999,999,999};
float[]   cacheFzoom  = {999,999,999,999};
int[]     cacheFMode  = {-1,-1,-1,-1};
float[]   cacheFCut   = {-1,-1,-1,-1};
boolean[] cacheInv    = {false,false,false,false};
float     cacheZoomX  = -1;
float     cachePanOff = -1e9;

// Trigger
boolean trigEnabled = false;
int     trigCh      = 0;
boolean trigRising  = true;
float   trigLevel   = 350;
boolean trigArmed   = true;
int     trigPos     = 0;

// Curseurs
float cx1=280, cx2=680, cy1=180, cy2=520;
int   dragCursor=-1;
float cur_dt=0, cur_df=0, cur_dv=0, cur_v1=0, cur_v2=0;

// Zoom / Pan
float   zoomX=1.0, panOffsetX=0.0;
boolean isPanning=false;
float   panStartX, panStartOff;

// Mesures  {Vmax,Vmin,Vpp,Vrms,Freq,Period}
float[][] measures   = new float[NUM_CH][6];
float[]   freqSmooth = {0,0,0,0};
final float FREQ_ALPHA=0.15;

// Compteur de samples reçus (pour invalidation cache)
long globalSampleCount = 0;
long[] chSampleCount   = new long[NUM_CH];

// Compteur de frames pour throttler les calculs coûteux (mesures, FFT)
int measureFrameCount = 0;
final int MEASURE_EVERY = 6;  // recalcule les mesures tous les 6 frames (~10 Hz à 60 fps)

// FFT cache — résolution FFT_BINS (512 bins, power-of-2)
boolean fftDirty = true;
float[][] fftCache = new float[NUM_CH][FFT_SIZE/2];

// ═══════════════════════════════════════════════════════════════════════════
//  SETUP
// ═══════════════════════════════════════════════════════════════════════════
void setup() {
  size(1440, 900);
  smooth(4);  // réduit de 8 à 4 pour gain perf
  surface.setTitle("EPT TEKLAB 4000 v8.0");
  frameRate(60);

  applyTheme();

  for (int i=0;i<NUM_CH;i++) {
    // Pré-remplir avec 2048 (milieu de plage ADC = ligne plate au centre)
    for (int j=0;j<BUFFER_SIZE;j++) rawHist[i][j]=2048;
    ringHead[i]=0;
    computeBwCoeff(i);
  }

  // Pré-calculer la fenêtre Hann une seule fois
  for (int i=0;i<FFT_SIZE;i++) hannWindow[i]=0.5*(1-cos(TWO_PI*i/(FFT_SIZE-1)));

  gScreen = createGraphics(SCREEN_W, SCREEN_H);
  buildBezel();
  buildGrid();       // grille pré-rendue une seule fois
  buildLogoEPT();    // logo : tente GIF externe, sinon vectoriel

  cp5 = new ControlP5(this);
  PFont pf = createFont("Consolas", 10, true);
  cp5.setFont(new ControlFont(pf, 10));
  buildUI();
  cp5.hide();

  printArray(Serial.list());
  try {
    monPort = new Serial(this, "COM8", BAUD_RATE);
    // Buffer interne 4096 octets : absorbe les rafales à 921600 bps sans perte
    monPort.buffer(4096);
    monPort.bufferUntil('\n');
    rateLastMillis = millis();
    println("[OK] COM8 connecté @ "+BAUD_RATE+" bps");
  } catch (Exception e) {
    monPort=null;
    demoLastMs = millis();
    println("[INFO] COM8 absent — mode démo "+DEMO_SPS+" SPS");
  }

  splashStart = millis();
}

// ═══════════════════════════════════════════════════════════════════════════
//  LOGO EPT — charge EPT_logo.gif si disponible, sinon logo vectoriel
// ═══════════════════════════════════════════════════════════════════════════
void buildLogoEPT() {
  int LW=260, LH=260;
  gLogo = createGraphics(LW, LH);
  gLogo.beginDraw();
  gLogo.clear();

  // ── Tente de charger le fichier GIF externe ──────────────────────────────
  // Chemin absolu Windows ou relatif au sketch (data/)
  PImage gifImg = null;
  String[] gifPaths = {
    "C:\\Users\\omarb\\Desktop\\EPT_logo.gif",
    sketchPath("EPT_logo.gif"),
    dataPath("EPT_logo.gif")
  };
  for (String p : gifPaths) {
    try {
      PImage tmp = loadImage(p);
      if (tmp != null && tmp.width > 0) { gifImg = tmp; break; }
    } catch (Exception e) { /* try next */ }
  }

  if (gifImg != null) {
    // ── GIF chargé : on le redimensionne dans le PGraphics ─────────────────
    gLogo.image(gifImg, 0, 0, LW, LH);
    println("[OK] Logo EPT chargé depuis GIF : " + gifImg.width + "×" + gifImg.height);
  } else {
    // ── Fallback : logo vectoriel généré ────────────────────────────────────
    println("[INFO] EPT_logo.gif introuvable — logo vectoriel utilisé");

    // Fond circulaire gradient (vert sombre → transparent)
    gLogo.noStroke();
    for (int r=LW/2;r>0;r-=2) {
      float f=(float)r/(LW/2.0);
      gLogo.fill(20,160,60, (int)(80*(1-f)));
      gLogo.ellipse(LW/2,LH/2,r*2,r*2);
    }

    // Cercle extérieur double
    gLogo.noFill();
    gLogo.stroke(50,220,90,240); gLogo.strokeWeight(4);
    gLogo.ellipse(LW/2,LH/2,LW-8,LH-8);
    gLogo.stroke(30,180,60,140); gLogo.strokeWeight(1.5);
    gLogo.ellipse(LW/2,LH/2,LW-18,LH-18);

    // Lettres "EPT" en gros
    gLogo.fill(255,255,255,245);
    gLogo.textAlign(PGraphics.CENTER,PGraphics.CENTER);
    gLogo.textSize(80);
    gLogo.text("EPT",LW/2,LH/2-12);

    // Sous-titre
    gLogo.fill(180,240,190,210);
    gLogo.textSize(14);
    gLogo.text("INSTRUMENTS",LW/2,LH/2+52);

    // Trait décoratif
    gLogo.stroke(50,220,90,180); gLogo.strokeWeight(1.5);
    gLogo.line(LW/2-55,LH/2+36,LW/2+55,LH/2+36);

    // Points cardinaux
    gLogo.fill(50,220,90,200); gLogo.noStroke();
    gLogo.ellipse(LW/2,12,6,6);
    gLogo.ellipse(LW/2,LH-12,6,6);
    gLogo.ellipse(12,LH/2,6,6);
    gLogo.ellipse(LW-12,LH/2,6,6);
  }

  gLogo.endDraw();
}

// ═══════════════════════════════════════════════════════════════════════════
//  GRILLE CRT PRÉ-RENDUE
// ═══════════════════════════════════════════════════════════════════════════
void buildGrid() {
  gGrid = createGraphics(SCREEN_W, SCREEN_H);
  gGrid.beginDraw();
  gGrid.clear();
  int dX=12,dY=10;
  float sX=(float)SCREEN_W/dX, sY=(float)SCREEN_H/dY;

  gGrid.stroke(C_GRID_FINE); gGrid.strokeWeight(0.4);
  for(int i=0;i<=dX*5;i++) gGrid.line(i*sX/5,0,i*sX/5,SCREEN_H);
  for(int i=0;i<=dY*5;i++) gGrid.line(0,i*sY/5,SCREEN_W,i*sY/5);

  gGrid.stroke(C_GRID_MED); gGrid.strokeWeight(0.8);
  for(int i=0;i<=dX;i++) gGrid.line(i*sX,0,i*sX,SCREEN_H);
  for(int i=0;i<=dY;i++) gGrid.line(0,i*sY,SCREEN_W,i*sY);

  gGrid.stroke(C_GRID_CENTER); gGrid.strokeWeight(1.2);
  gGrid.line(0,SCREEN_H/2,SCREEN_W,SCREEN_H/2);
  gGrid.line(SCREEN_W/2,0,SCREEN_W/2,SCREEN_H);

  gGrid.stroke(C_GRID_MED); gGrid.strokeWeight(0.8);
  for(int i=0;i<=dX*5;i++){float x=i*sX/5;float l=(i%5==0)?8:4;gGrid.line(x,SCREEN_H/2-l,x,SCREEN_H/2+l);}
  for(int i=0;i<=dY*5;i++){float y=i*sY/5;float l=(i%5==0)?8:4;gGrid.line(SCREEN_W/2-l,y,SCREEN_W/2+l,y);}

  gGrid.endDraw();
}

// ═══════════════════════════════════════════════════════════════════════════
//  COEFFICIENTS BUTTERWORTH — pré-calculés, recalculés si fc change
// ═══════════════════════════════════════════════════════════════════════════
void computeBwCoeff(int ch) {
  float fc  = constrain(filterCutoff[ch],0.001,0.499);
  float wd  = tan(PI*fc);
  float k   = wd*wd;
  float sq2 = sqrt(2.0);
  float norm= 1.0/(1.0+sq2*wd+k);
  bwCoeff[ch][0] = k*norm;           // b0
  bwCoeff[ch][1] = 2*bwCoeff[ch][0]; // b1
  bwCoeff[ch][2] = bwCoeff[ch][0];   // b2
  bwCoeff[ch][3] = 2*(k-1)*norm;     // a1
  bwCoeff[ch][4] = (1-sq2*wd+k)*norm;// a2
  bwFcLast[ch]   = fc;
  // Réinitialiser les états IIR
  bwX1[ch][0]=bwX2[ch][0]=bwY1[ch][0]=bwY2[ch][0]=0;
}

// ═══════════════════════════════════════════════════════════════════════════
//  FILTRES OPTIMISÉS
// ═══════════════════════════════════════════════════════════════════════════

// Butterworth : utilise les coeffs pré-calculés
float[] applyButterworth(float[] sig, int ch) {
  // Recalcule les coeffs seulement si fc a changé
  if (abs(filterCutoff[ch]-bwFcLast[ch])>1e-5) computeBwCoeff(ch);
  float b0=bwCoeff[ch][0],b1=bwCoeff[ch][1],b2=bwCoeff[ch][2];
  float a1=bwCoeff[ch][3],a2=bwCoeff[ch][4];
  float[] out=new float[sig.length];
  float x1=bwX1[ch][0],x2=bwX2[ch][0],y1=bwY1[ch][0],y2=bwY2[ch][0];
  for(int i=0;i<sig.length;i++){
    float x0=sig[i];
    float y0=b0*x0+b1*x1+b2*x2-a1*y1-a2*y2;
    out[i]=y0; x2=x1; x1=x0; y2=y1; y1=y0;
  }
  bwX1[ch][0]=x1;bwX2[ch][0]=x2;bwY1[ch][0]=y1;bwY2[ch][0]=y2;
  return out;
}

// Médian optimisé : tri par sélection partielle (O(N·w/2) au lieu de O(N·w·log(w)))
float[] applyMedian(float[] sig, int ch) {
  int w=filterWindow[ch], hw=w/2;
  float[] out=new float[sig.length];
  float[] buf=new float[w];
  int med=w/2;
  for(int i=0;i<sig.length;i++){
    for(int j=0;j<w;j++) buf[j]=sig[constrain(i-hw+j,0,sig.length-1)];
    // Sélection partielle jusqu'au med+1 ème élément (plus rapide que sort complet)
    for(int j=0;j<=med;j++){
      int minIdx=j;
      for(int k=j+1;k<w;k++) if(buf[k]<buf[minIdx]) minIdx=k;
      float tmp=buf[j]; buf[j]=buf[minIdx]; buf[minIdx]=tmp;
    }
    out[i]=buf[med];
  }
  return out;
}

// Moyenne glissante : version accumulatrice O(N) au lieu de O(N·w)
float[] applyMovingAverage(float[] sig, int ch) {
  int w=filterWindow[ch], hw=w/2, N=sig.length;
  float[] out=new float[N];
  // Somme initiale
  float sum=0; int cnt=0;
  for(int j=0;j<hw+1&&j<N;j++){sum+=sig[j];cnt++;}
  // Glissière O(N)
  for(int i=0;i<N;i++){
    if(i+hw<N){sum+=sig[i+hw];cnt++;}
    out[i]=sum/cnt;
    if(i-hw>=0){sum-=sig[i-hw];cnt--;}
  }
  return out;
}

float[] applyFilter(float[] sig,int ch){
  switch(filterMode[ch]){
    case 1: return applyButterworth(sig,ch);
    case 2: return applyMedian(sig,ch);
    case 3: return applyMovingAverage(sig,ch);
    default: return sig;
  }
}

// ═══════════════════════════════════════════════════════════════════════════
//  SIGNAL AVEC CACHE — recalcul uniquement si paramètres ou data changent
// ═══════════════════════════════════════════════════════════════════════════
boolean needsRecompute(int ch){
  if(!cacheValid[ch]) return true;
  if(chSampleCount[ch]!=lastSample[ch]) return true;
  if(posY[ch]!=cachePosY[ch]) return true;
  if(gain[ch]!=cacheGain[ch]) return true;
  if(fzoom[ch]!=cacheFzoom[ch]) return true;
  if(filterMode[ch]!=cacheFMode[ch]) return true;
  if(abs(filterCutoff[ch]-cacheFCut[ch])>1e-5) return true;
  if(inv[ch]!=cacheInv[ch]) return true;
  if(abs(zoomX-cacheZoomX)>1e-5) return true;
  if(abs(panOffsetX-cachePanOff)>1e-3) return true;
  return false;
}

void invalidateCache(int ch){
  cacheValid[ch]=false;
  fftDirty=true;
}

void invalidateAllCaches(){
  for(int i=0;i<NUM_CH;i++) cacheValid[i]=false;
  fftDirty=true;
}

float[] getProcessedSignal(int ch){
  if(!needsRecompute(ch)) return sigCache[ch];

  float ezoom=fzoom[ch]*zoomX, winSz=SCREEN_W/ezoom;

  // ── Lecture correcte du buffer circulaire ────────────────────────────────
  // ringHead[ch] = prochaine case À ÉCRIRE  →  oldest = ringHead, newest = ringHead-1
  // On veut afficher les winSz derniers échantillons, avec pan optionnel.
  // startSample = index DANS LE BUFFER (0..BUFFER_SIZE-1) du premier sample affiché.
  float baseStart = (trigEnabled&&!trigArmed&&trigCh==ch)
                    ? trigPos - winSz/2.0
                    : BUFFER_SIZE - winSz;
  float startIdx = constrain(baseStart - panOffsetX, 0, BUFFER_SIZE - winSz);

  float[] raw = new float[SCREEN_W];
  for(int x=0;x<SCREEN_W;x++){
    // position chronologique dans la fenêtre affichée (0 = plus ancien)
    int chronoIdx = constrain((int)map(x,0,SCREEN_W-1,startIdx,startIdx+winSz-1),
                              0, BUFFER_SIZE-1);
    // conversion vers l'index physique dans le tableau circulaire
    // ringHead est le "plus vieux+1" → oldest=ringHead → offset=chronoIdx
    int physIdx = (ringHead[ch] + chronoIdx) % BUFFER_SIZE;
    float v = rawHist[ch][physIdx];
    if(inv[ch]) v = 4095 - v;
    raw[x] = v;
  }

  float[] filtered = applyFilter(raw, ch);
  for(int x=0;x<SCREEN_W;x++){
    float scaled = ((filtered[x]-2048)*gain[ch])+2048;
    sigCache[ch][x] = map(scaled, 0, 4095, SCREEN_H, 0) - posY[ch];
  }
  cacheValid[ch]   = true;
  lastSample[ch]   = chSampleCount[ch];
  cachePosY[ch]    = posY[ch];   cacheGain[ch]  = gain[ch];
  cacheFzoom[ch]   = fzoom[ch];  cacheFMode[ch] = filterMode[ch];
  cacheFCut[ch]    = filterCutoff[ch]; cacheInv[ch] = inv[ch];
  cacheZoomX       = zoomX;      cachePanOff    = panOffsetX;
  fftDirty = true;
  return sigCache[ch];
}

// ═══════════════════════════════════════════════════════════════════════════
//  MESURES
// ═══════════════════════════════════════════════════════════════════════════
float[] computeMeasures(int ch,float[] sig){
  int N=sig.length;
  float[] sorted=sig.clone(); Arrays.sort(sorted);
  float mn=sorted[(int)(N*0.02)],mx=sorted[(int)(N*0.98)];
  float rz=SCREEN_H/2.0-posY[ch],vppx=TENSION_BASE/50.0;
  float vMax=(rz-mn)*vppx/gain[ch],vMin=(rz-mx)*vppx/gain[ch],vpp=vMax-vMin;
  double sumSq=0;
  for(int i=0;i<N;i++){double v=(rz-sig[i])*vppx/gain[ch];sumSq+=v*v;}
  float vrms=(float)Math.sqrt(sumSq/N);
  float freq=computeFrequency(ch,sig);
  if(freq>0) freqSmooth[ch]=FREQ_ALPHA*freq+(1-FREQ_ALPHA)*freqSmooth[ch];
  else       freqSmooth[ch]*=0.95;
  float period=(freqSmooth[ch]>0)?1000.0/freqSmooth[ch]:0;
  return new float[]{vMax,vMin,vpp,vrms,freqSmooth[ch],period};
}

// ═══════════════════════════════════════════════════════════════════════════
//  FRÉQUENCE — ZCR + Autocorrélation + Interpolation parabolique
// ═══════════════════════════════════════════════════════════════════════════
float computeFrequency(int ch,float[] signal){
  int N=signal.length;
  float mean=0; for(int i=0;i<N;i++) mean+=signal[i]; mean/=N;
  float[] s=new float[N];float mn=signal[0],mx=signal[0];
  for(int i=0;i<N;i++){s[i]=signal[i]-mean;if(signal[i]<mn)mn=signal[i];if(signal[i]>mx)mx=signal[i];}
  if(mx-mn<8) return 0;

  float thr=(mx-mn)*0.05;
  int[] cr=new int[N];int nCr=0;boolean above=s[0]>thr;
  for(int i=1;i<N;i++){
    if(above&&s[i]<-thr){cr[nCr++]=i;above=false;}
    else if(!above&&s[i]>thr) above=true;
  }
  float freqZCR=0;
  if(nCr>=2){
    float mP=(float)(cr[nCr-1]-cr[0])/(nCr-1);
    float ez=fzoom[ch]*zoomX,secPx=(SCREEN_W/ez)/(SCREEN_W*SAMPLE_RATE);
    if(mP*secPx>0) freqZCR=1.0/(mP*secPx);
  }
  float ac0=0;for(int i=0;i<N;i++) ac0+=s[i]*s[i];
  if(ac0==0) return freqZCR;

  int lagMin=4,lagMax=N/2;
  if(freqZCR>0){
    float ez=fzoom[ch]*zoomX,pxPS=SCREEN_W/(SCREEN_W/ez);
    float lagEst=SAMPLE_RATE/freqZCR/pxPS;
    lagMin=max(4,(int)(lagEst*0.4));lagMax=min(N/2,(int)(lagEst*2.5));
  }
  float bCorr=-1;int bLag=-1;
  for(int lag=lagMin;lag<=lagMax;lag++){
    float ac=0;int cnt=N-lag;
    for(int i=0;i<cnt;i++) ac+=s[i]*s[i+lag];
    ac/=(ac0*(float)cnt/N);
    if(ac>bCorr){bCorr=ac;bLag=lag;}
    if(bLag>lagMin&&lag>bLag+20&&bCorr>0.5) break;
  }
  if(bLag<3||bCorr<0.3) return freqZCR;

  float lagFine=bLag;
  if(bLag>1&&bLag<lagMax-1){
    float am=0,a0=0,ap=0;
    for(int i=0;i<N-bLag+1;i++) am+=s[i]*s[i+bLag-1];
    for(int i=0;i<N-bLag;i++)   a0+=s[i]*s[i+bLag];
    for(int i=0;i<N-bLag-1;i++) ap+=s[i]*s[i+bLag+1];
    am/=(ac0*(float)(N-bLag+1)/N);a0/=(ac0*(float)(N-bLag)/N);ap/=(ac0*(float)(N-bLag-1)/N);
    float denom=am-2*a0+ap;
    if(abs(denom)>1e-6) lagFine=bLag-0.5*(ap-am)/denom;
  }
  float ez2=fzoom[ch]*zoomX,pxPS2=SCREEN_W/(SCREEN_W/ez2);
  return SAMPLE_RATE/(lagFine/pxPS2);
}

// ═══════════════════════════════════════════════════════════════════════════
//  CURSEURS
// ═══════════════════════════════════════════════════════════════════════════
void updateCursorValues(){
  int refCh=0;for(int i=0;i<NUM_CH;i++){if(active[i]){refCh=i;break;}}
  float ez=fzoom[refCh]*zoomX,secPx=(SCREEN_W/ez)/(SCREEN_W*SAMPLE_RATE);
  cur_dt=(cx2-cx1)*secPx*1000;
  cur_df=(abs(cur_dt)>0.0001)?1000.0/abs(cur_dt):0;
  float vppx=TENSION_BASE/50.0/gain[refCh],rz=SCREEN_H/2.0-posY[refCh];
  cur_v1=(rz-cy1)*vppx; cur_v2=(rz-cy2)*vppx; cur_dv=cur_v2-cur_v1;
}

// ═══════════════════════════════════════════════════════════════════════════
//  SIGNAL DÉMO
// ═══════════════════════════════════════════════════════════════════════════
// ═══════════════════════════════════════════════════════════════════════════
//  SIGNAL DÉMO — cadencé millis(), pré-rempli dès le premier appel
//  Injecte les trames manquées depuis le dernier appel (précis comme Arduino)
// ═══════════════════════════════════════════════════════════════════════════
float demoPhase  = 0;
boolean demoInit = false;   // pré-remplissage unique au 1er appel

void injectDemoSignal(){
  if(!runOscillo) return;

  long now     = millis();
  float phaseStep = TWO_PI * 5.0 / DEMO_SPS;   // 5 Hz fondamental

  // ── Pré-remplissage complet au premier appel ─────────────────────────────
  // Remplit tout le ring buffer pour avoir un signal visible immédiatement,
  // même avant que le premier sample réel soit injecté.
  if(!demoInit){
    for(int s=0; s<BUFFER_SIZE; s++){
      demoPhase += phaseStep;
      for(int i=0;i<NUM_CH;i++){
        float sig;
        switch(i){
          case 0: sig=2048+1800*sin(demoPhase);                                       break;
          case 1: sig=2048+1400*sin(demoPhase*2+0.5)+280*sin(demoPhase*6);            break;
          case 2: sig=2048+1000*sin(demoPhase*3+1.2);                                 break;
          default:sig=2048+ 700*sin(demoPhase*0.5+2.1);                               break;
        }
        rawHist[i][ringHead[i]] = constrain(sig, 0, 4095);
        ringHead[i] = (ringHead[i]+1) % BUFFER_SIZE;
      }
    }
    demoInit    = true;
    demoLastMs  = now;
    rateLastMillis = now;
    invalidateAllCaches();
    return;
  }

  // ── Injection cadencée sur millis() ─────────────────────────────────────
  long elapsed = now - demoLastMs;
  if(elapsed <= 0){ invalidateAllCaches(); return; }

  int framesToInject = (int)(DEMO_SPS * elapsed / 1000.0);
  // Si pas encore 1 frame entière à injecter, on attend (mais on force quand
  // même un redraw pour ne pas figer l'écran)
  if(framesToInject < 1){ invalidateAllCaches(); return; }

  demoLastMs = now;

  for(int f=0; f<framesToInject; f++){
    demoPhase += phaseStep;
    float[] v = {
      2048 + 1800*sin(demoPhase)             + randomGaussian()*18,
      2048 + 1400*sin(demoPhase*2  + 0.5)    + randomGaussian()*22 + 280*sin(demoPhase*6),
      2048 + 1000*sin(demoPhase*3  + 1.2)    + randomGaussian()*28,
      2048 +  700*sin(demoPhase*0.5+ 2.1)    + randomGaussian()*32
    };
    for(int i=0;i<NUM_CH;i++){
      if(active[i]){
        rawHist[i][ringHead[i]] = constrain(v[i], 0, 4095);
        ringHead[i] = (ringHead[i]+1) % BUFFER_SIZE;
        chSampleCount[i]++;
      }
    }
    globalSampleCount++;
    rateCountSamples++;
  }

  // ── Auto-mesure SAMPLE_RATE ──────────────────────────────────────────────
  long ratElapsed = now - rateLastMillis;
  if(ratElapsed >= RATE_WINDOW_MS && rateCountSamples > 0){
    measuredSPS    = rateCountSamples * 1000.0 / ratElapsed;
    SAMPLE_RATE    = measuredSPS;
    rateCountSamples = 0;
    rateLastMillis   = now;
  }

  if(trigEnabled && trigArmed) searchTrigger();
  invalidateAllCaches();
}

// ═══════════════════════════════════════════════════════════════════════════
//  DRAW
// ═══════════════════════════════════════════════════════════════════════════
void draw(){
  // Injecter le signal démo à chaque frame (avant ET après le splash)
  if(monPort==null && powerOn) injectDemoSignal();

  if(showSplash){
    drawSplash();
    if(millis()-splashStart>=3800){showSplash=false;cp5.show();}
    return;
  }
  drawMain();
}

// ═══════════════════════════════════════════════════════════════════════════
//  SPLASH — logo EPT vectoriel centré + animation fluide
// ═══════════════════════════════════════════════════════════════════════════
void drawSplash(){
  background(C_APP_BG);
  float t=(millis()-splashStart)/1000.0;
  float alpha=constrain(map(t,0,0.6,0,255),0,255);
  float sc=lerp(0.3,1.0,constrain(t/0.8,0,1));

  // Halo vert de fond
  noStroke();
  for(int r=440;r>0;r-=5){
    float f=r/440.0;
    if(darkMode) fill(0,(int)(28*(1-f)),(int)(8*(1-f)),255);
    else         fill(218,228,242,(int)(175*(1-f)));
    ellipse(width/2,height/2,r*2,r*2);
  }

  // Logo EPT vectoriel (toujours disponible)
  imageMode(CENTER);
  tint(255,alpha);
  image(gLogo,width/2,height/2-55,(int)(260*sc),(int)(260*sc));
  noTint();
  imageMode(CORNER);

  // Texte
  textAlign(CENTER,CENTER);
  fill(C_TEXT_ACCENT,alpha);
  textSize(30);
  text("TEKLAB 4000",width/2,height/2+98);
  fill(C_TEXT_DIM,alpha);
  textSize(13);
  text("OSCILLOSCOPE NUMÉRIQUE 4 VOIES  —  EPT INSTRUMENTS",width/2,height/2+128);
  textSize(10);
  fill(C_TEXT_DIM,alpha*0.65);
  text("v8.0  |  921600 bps  |  FFT Cooley-Tukey  |  Auto-SPS  |  Parser robuste",width/2,height/2+146);
  text("F = Plein écran     T = Thème     Espace = RUN/STOP",width/2,height/2+162);

  // Barre de progression
  float prog=constrain(t/3.2,0,1);
  noFill();stroke(C_TEXT_DIM,82);strokeWeight(1);
  rect(width/2-155,height/2+192,310,6,3);
  noStroke();fill(C_BTN_RUN,alpha);
  rect(width/2-155,height/2+192,310*prog,6,3);
  // % progression
  fill(C_TEXT_DIM,alpha*0.7);textSize(10);
  text(nf(prog*100,0,0)+"%",width/2,height/2+214);

  textAlign(LEFT,BASELINE);
}

// ═══════════════════════════════════════════════════════════════════════════
//  DESSIN PRINCIPAL
// ═══════════════════════════════════════════════════════════════════════════
void drawMain(){
  measureFrameCount++;
  background(C_APP_BG);
  drawChassis();
  if(showCursors) updateCursorValues();
  renderCRTScreen();
  image(gScreen,SCREEN_X,SCREEN_Y);
  image(gBezel, SCREEN_X,SCREEN_Y);
  drawMeasureBar();
  drawRightPanel();
  drawStatusBar();
}

// ═══════════════════════════════════════════════════════════════════════════
//  BEZEL
// ═══════════════════════════════════════════════════════════════════════════
void buildBezel(){
  gBezel=createGraphics(SCREEN_W,SCREEN_H);
  gBezel.beginDraw();gBezel.clear();
  int bw=SCREEN_W,bh=SCREEN_H;
  for(int r=min(bw,bh)/2;r>0;r-=3){
    float f=1.0-(float)r/(min(bw,bh)/2.0);
    gBezel.stroke(0,0,0,(int)(f*f*145));gBezel.strokeWeight(3);gBezel.noFill();
    gBezel.rect(r,r,bw-2*r,bh-2*r);
  }
  gBezel.noFill();gBezel.strokeWeight(2.5);gBezel.stroke(56,68,80);
  gBezel.rect(0,0,bw,bh,10);
  gBezel.strokeWeight(1);gBezel.stroke(90,106,120,106);
  gBezel.line(10,1,bw-10,1);gBezel.line(1,10,1,bh-10);
  gBezel.stroke(8,10,12,145);
  gBezel.line(bw-1,10,bw-1,bh-10);gBezel.line(10,bh-1,bw-10,bh-1);
  gBezel.endDraw();
}

// ═══════════════════════════════════════════════════════════════════════════
//  CHÂSSIS
// ═══════════════════════════════════════════════════════════════════════════
void drawChassis(){
  noStroke();fill(C_CHASSIS);rect(0,0,width,height);
  stroke(darkMode?color(32,38,46,18):color(172,182,196,26));strokeWeight(1);
  for(int y=0;y<height;y+=3) line(0,y,width,y);
  noStroke();
  fill(darkMode?color(60,72,84):color(196,206,218));rect(0,0,width,2);
  fill(darkMode?color(40,48,58):color(180,192,206));rect(0,height-2,width,2);
  fill(C_PANEL_BORDER);rect(SCREEN_X+SCREEN_W+6,0,2,height);
}

// ═══════════════════════════════════════════════════════════════════════════
//  RENDU ÉCRAN CRT — grille depuis PGraphics pré-rendu
// ═══════════════════════════════════════════════════════════════════════════
void renderCRTScreen(){
  gScreen.beginDraw();
  if(!powerOn){
    gScreen.background(2,3,2);
    gScreen.fill(darkMode?color(35,50,35,172):color(155,175,155,115));
    gScreen.textAlign(PGraphics.CENTER,PGraphics.CENTER);gScreen.textSize(20);
    gScreen.text("INSTRUMENT HORS TENSION",SCREEN_W/2,SCREEN_H/2);
    gScreen.endDraw();return;
  }
  gScreen.background(C_SCREEN_BG);

  // Lueur phosphore (sombre)
  if(darkMode){
    for(int r=SCREEN_H;r>0;r-=8){
      float f=1.0-(float)r/SCREEN_H;
      gScreen.fill(0,(int)(8*f*f),(int)(2*f*f),22);gScreen.noStroke();
      gScreen.ellipse(SCREEN_W/2,SCREEN_H/2,r*2,r);
    }
  }

  // Grille depuis PGraphics pré-rendu
  gScreen.image(gGrid,0,0);

  // Scan-lines légères — un seul rect semi-transparent au lieu de SCREEN_H/2 lignes
  if(darkMode){
    gScreen.noStroke();
    gScreen.fill(0,0,0,9);
    gScreen.rect(0,0,SCREEN_W,SCREEN_H);
  }

  if(showFFT) drawFFTView(gScreen);
  else{
    drawSignals(gScreen);
    if(trigEnabled) drawTriggerLine(gScreen);
    if(showCursors) drawCursorsOverlay(gScreen);
  }

  // Labels
  gScreen.fill(C_TEXT_DIM,162);gScreen.textSize(10);
  gScreen.textAlign(PGraphics.LEFT,PGraphics.TOP);
  gScreen.text(showFFT?"MODE FFT":"MODE TEMPOREL",8,8);
  if(zoomX!=1.0){gScreen.fill(C_TEXT_ACCENT,192);gScreen.text("ZOOM ×"+nf(zoomX,1,2),8,22);}
  if(showCursors){
    gScreen.fill(darkMode?color(255,212,42,205):color(148,85,5,198));
    gScreen.textSize(9);gScreen.textAlign(PGraphics.LEFT,PGraphics.TOP);
    gScreen.text("● ÉCRAN GELÉ — CURSEURS ACTIFS",8,showFFT?22:36);
  }
  // Badges filtres
  int fx=8,fy=showFFT?22:36;if(showCursors)fy+=14;
  String[] fN={"","LP","MED","MA"};
  color[] fC={0,color(20,158,198),color(198,98,18),color(98,198,78)};
  for(int ch=0;ch<NUM_CH;ch++){
    if(filterMode[ch]>0){
      gScreen.fill(fC[filterMode[ch]],185);gScreen.textSize(9);
      gScreen.textAlign(PGraphics.LEFT,PGraphics.TOP);
      gScreen.text("CH"+(ch+1)+":"+fN[filterMode[ch]],fx,fy);fx+=50;
    }
  }
  gScreen.endDraw();
}

// ═══════════════════════════════════════════════════════════════════════════
//  SIGNAUX — rendu optimisé : 2 passes au lieu de 3, vertices pré-calculés
// ═══════════════════════════════════════════════════════════════════════════
void drawSignals(PGraphics pg){
  for(int ch=0;ch<NUM_CH;ch++){
    if(!active[ch]) continue;
    float[] sig=getProcessedSignal(ch);
    float zy=constrain(SCREEN_H/2.0-posY[ch],0,SCREEN_H);
    pg.stroke(CH_COLORS[ch],34);pg.strokeWeight(1);pg.line(0,zy,SCREEN_W,zy);
    pg.fill(CH_COLORS[ch],102);pg.noStroke();
    pg.triangle(0,zy-5,0,zy+5,10,zy);
    pg.fill(C_CHASSIS);pg.noStroke();pg.rect(12,zy-8,14,14,2);
    pg.fill(CH_COLORS[ch]);pg.textSize(10);
    pg.textAlign(PGraphics.CENTER,PGraphics.CENTER);
    pg.text(ch+1,19,zy+1);pg.textAlign(PGraphics.LEFT,PGraphics.BASELINE);

    // Pré-clipper les Y une seule fois (évite constrain() × SCREEN_W × 3 passes)
    float[] ys = new float[SCREEN_W];
    for(int x=0;x<SCREEN_W;x++) ys[x]=constrain(sig[x],0,SCREEN_H);

    // Recalcul des mesures throttlé : tous les MEASURE_EVERY frames seulement
    if(measureFrameCount % MEASURE_EVERY == 0) measures[ch]=computeMeasures(ch,sig);

    // Passe 1 : halo glow (strokeWeight large, alpha faible)
    pg.stroke(CH_COLORS[ch],28);pg.strokeWeight(4.5);pg.noFill();
    pg.beginShape();
    for(int x=0;x<SCREEN_W;x++) pg.vertex(x,ys[x]);
    pg.endShape();

    // Passe 2 : trait principal net
    pg.stroke(CH_COLORS[ch]);pg.strokeWeight(1.5);
    pg.beginShape();
    for(int x=0;x<SCREEN_W;x++) pg.vertex(x,ys[x]);
    pg.endShape();
  }
}

// ═══════════════════════════════════════════════════════════════════════════
//  FFT — calculée seulement si showFFT+signal changé
// ═══════════════════════════════════════════════════════════════════════════
void drawFFTView(PGraphics pg){
  int bins=FFT_BINS;  // 512 bins (power-of-2)
  for(int ch=0;ch<NUM_CH;ch++){
    if(!active[ch]) continue;
    float[] sig=getProcessedSignal(ch);
    // Recalcule uniquement si signal modifié
    if(fftDirty) fftCache[ch]=computeFFT(sig);
    float[] mag=fftCache[ch];
    pg.fill(CH_COLORS[ch]);pg.textSize(10);
    pg.textAlign(PGraphics.LEFT,PGraphics.BASELINE);
    pg.text("CH"+(ch+1),8,16+ch*14);
    pg.stroke(CH_COLORS[ch],50);pg.strokeWeight(3);pg.noFill();
    for(int k=1;k<bins;k++){
      float x0=map(k-1,0,bins,0,SCREEN_W),x1=map(k,0,bins,0,SCREEN_W);
      pg.line(x0,constrain(SCREEN_H-mag[k-1]*14,0,SCREEN_H),x1,constrain(SCREEN_H-mag[k]*14,0,SCREEN_H));
    }
    pg.stroke(CH_COLORS[ch]);pg.strokeWeight(1.2);
    for(int k=1;k<bins;k++){
      float x0=map(k-1,0,bins,0,SCREEN_W),x1=map(k,0,bins,0,SCREEN_W);
      pg.line(x0,constrain(SCREEN_H-mag[k-1]*14,0,SCREEN_H),x1,constrain(SCREEN_H-mag[k]*14,0,SCREEN_H));
    }
  }
  fftDirty=false;
  pg.fill(C_TEXT_DIM);pg.textSize(9);pg.textAlign(PGraphics.CENTER,PGraphics.BASELINE);
  for(int i=0;i<=6;i++){
    float fx=map(i,0,6,0,SCREEN_W),fv=map(i,0,6,0,SAMPLE_RATE/2);
    pg.text(nf(fv,0,0)+"Hz",fx,SCREEN_H-4);
  }
}

// ═══════════════════════════════════════════════════════════════════════════
//  FFT COOLEY-TUKEY RADIX-2 — O(N·logN) au lieu de O(N²·bins)
//  ~10× plus rapide qu'une DFT naïve sur 1024 points
// ═══════════════════════════════════════════════════════════════════════════
float[] computeFFT(float[] signal){
  int N = FFT_SIZE;
  int bins = FFT_BINS;

  // ── 1. Remplissage + fenêtre de Hann pré-calculée ────────────────────────
  float[] re = new float[N];
  float[] im = new float[N];
  float ctr  = SCREEN_H / 2.0;
  for(int i=0;i<N;i++){
    float s = (i < signal.length) ? (ctr - signal[i]) : 0.0;
    re[i] = s * hannWindow[i];   // hannWindow pré-calculé dans setup()
    im[i] = 0.0;
  }

  // ── 2. Bit-reversal permutation ──────────────────────────────────────────
  int bits = (int)(Math.log(N)/Math.log(2));
  for(int i=0;i<N;i++){
    int rev=0, x=i;
    for(int b=0;b<bits;b++){rev=(rev<<1)|(x&1);x>>=1;}
    if(rev>i){
      float t=re[i];re[i]=re[rev];re[rev]=t;
      t=im[i];im[i]=im[rev];im[rev]=t;
    }
  }

  // ── 3. Papillon Cooley-Tukey ─────────────────────────────────────────────
  for(int len=2;len<=N;len<<=1){
    float ang = -TWO_PI/len;
    float wRe = cos(ang), wIm = sin(ang);
    for(int i=0;i<N;i+=len){
      float uRe=1.0, uIm=0.0;
      for(int j=0;j<len/2;j++){
        int u=i+j, v=i+j+len/2;
        float eRe=re[v]*uRe-im[v]*uIm;
        float eIm=re[v]*uIm+im[v]*uRe;
        re[v]=re[u]-eRe; im[v]=im[u]-eIm;
        re[u]+=eRe;      im[u]+=eIm;
        float nuRe=uRe*wRe-uIm*wIm;
        uIm=uRe*wIm+uIm*wRe;
        uRe=nuRe;
      }
    }
  }

  // ── 4. Magnitudes normalisées (bins positifs seulement) ──────────────────
  float[] mag = new float[bins];
  float norm = N / 2.0;
  for(int k=0;k<bins;k++){
    mag[k] = sqrt(re[k]*re[k]+im[k]*im[k]) / norm;
  }
  return mag;
}

// ═══════════════════════════════════════════════════════════════════════════
//  TRIGGER LINE
// ═══════════════════════════════════════════════════════════════════════════
void drawTriggerLine(PGraphics pg){
  pg.stroke(255,150,0,190);pg.strokeWeight(1);
  for(int x=0;x<SCREEN_W;x+=16) pg.line(x,trigLevel,x+8,trigLevel);
  pg.fill(255,150,0);pg.noStroke();
  pg.triangle(SCREEN_W-1,trigLevel,SCREEN_W-12,trigLevel-5,SCREEN_W-12,trigLevel+5);
  pg.textSize(10);pg.textAlign(PGraphics.RIGHT,PGraphics.BASELINE);
  pg.text("T"+(trigRising?"▲":"▼"),SCREEN_W-14,trigLevel-4);
  pg.fill(trigArmed?color(255,150,0):color(45,210,70));
  pg.ellipse(SCREEN_W-14,SCREEN_H-14,9,9);
  pg.fill(C_TEXT_MAIN);pg.textSize(9);
  pg.text(trigArmed?"ARMÉ":"DÉCL.",SCREEN_W-14,SCREEN_H-22);
  pg.textAlign(PGraphics.LEFT,PGraphics.BASELINE);
}

// ═══════════════════════════════════════════════════════════════════════════
//  CURSEURS — valeurs temps réel sur l'écran
// ═══════════════════════════════════════════════════════════════════════════
void drawCursorsOverlay(PGraphics pg){
  color cX1=color(255,226,52),cX2=color(52,226,206);
  color cY1=color(255,136,55),cY2=color(95,175,255);

  // X1
  pg.stroke(cX1,215);pg.strokeWeight(1.6);
  for(int y=0;y<SCREEN_H;y+=12) pg.line(cx1,y,cx1,y+7);
  pg.noStroke();pg.fill(cX1,225);pg.rect(cx1-26,3,52,18,4);
  pg.fill(0);pg.textSize(9);pg.textAlign(PGraphics.CENTER,PGraphics.CENTER);
  pg.text("X1 "+nf(cx1,0,0)+"px",cx1,12);

  // X2
  pg.stroke(cX2,215);pg.strokeWeight(1.6);
  for(int y=0;y<SCREEN_H;y+=12) pg.line(cx2,y,cx2,y+7);
  pg.noStroke();pg.fill(cX2,225);pg.rect(cx2-26,3,52,18,4);
  pg.fill(0);pg.textSize(9);pg.textAlign(PGraphics.CENTER,PGraphics.CENTER);
  pg.text("X2 "+nf(cx2,0,0)+"px",cx2,12);

  // Y1
  pg.stroke(cY1,215);pg.strokeWeight(1.6);
  for(int x=0;x<SCREEN_W;x+=12) pg.line(x,cy1,x+7,cy1);
  float by1=constrain(cy1-22,3,SCREEN_H-24);
  pg.noStroke();pg.fill(cY1,225);pg.rect(3,by1,86,18,4);
  pg.fill(0);pg.textSize(9);pg.textAlign(PGraphics.LEFT,PGraphics.CENTER);
  pg.text("Y1="+nf(cur_v1,1,3)+"V",7,by1+9);

  // Y2
  pg.stroke(cY2,215);pg.strokeWeight(1.6);
  for(int x=0;x<SCREEN_W;x+=12) pg.line(x,cy2,x+7,cy2);
  float by2=constrain(cy2+4,3,SCREEN_H-24);
  pg.noStroke();pg.fill(cY2,225);pg.rect(3,by2,86,18,4);
  pg.fill(0);pg.textSize(9);pg.textAlign(PGraphics.LEFT,PGraphics.CENTER);
  pg.text("Y2="+nf(cur_v2,1,3)+"V",7,by2+9);

  // Panneau delta centré
  float px=constrain((cx1+cx2)/2-74,3,SCREEN_W-152);
  float py=SCREEN_H-98;
  pg.noStroke();
  pg.fill(darkMode?color(0,0,0,200):color(242,246,255,215));
  pg.rect(px,py,150,90,7);
  pg.stroke(cX1,142);pg.strokeWeight(1);pg.noFill();pg.rect(px,py,150,90,7);
  pg.noStroke();pg.textAlign(PGraphics.LEFT,PGraphics.CENTER);
  // Δt
  pg.fill(cX1);pg.textSize(9);pg.text("Δt",px+6,py+10);
  pg.fill(C_TEXT_MAIN);pg.textSize(11);pg.text(nf(cur_dt,1,2)+" ms",px+26,py+10);
  // Δf
  pg.fill(cX2);pg.textSize(9);pg.text("Δf",px+6,py+26);
  pg.fill(C_TEXT_MAIN);pg.textSize(11);pg.text(cur_df>0?nf(cur_df,1,2)+" Hz":"---",px+26,py+26);
  // Y1
  pg.fill(cY1);pg.textSize(9);pg.text("Y1",px+6,py+42);
  pg.fill(C_TEXT_MAIN);pg.textSize(11);pg.text(nf(cur_v1,1,3)+" V",px+26,py+42);
  // Y2
  pg.fill(cY2);pg.textSize(9);pg.text("Y2",px+6,py+58);
  pg.fill(C_TEXT_MAIN);pg.textSize(11);pg.text(nf(cur_v2,1,3)+" V",px+26,py+58);
  // ΔV
  pg.fill(C_TEXT_ACCENT);pg.textSize(11);
  pg.text("ΔV = "+nf(cur_dv,1,3)+" V",px+6,py+76);
  pg.textAlign(PGraphics.LEFT,PGraphics.BASELINE);
}

// ═══════════════════════════════════════════════════════════════════════════
//  BANDEAU MESURES
// ═══════════════════════════════════════════════════════════════════════════
void drawMeasureBar(){
  noStroke();fill(C_BEZEL);
  rect(SCREEN_X,SCREEN_Y+SCREEN_H+2,SCREEN_W,BASE_H-SCREEN_Y-SCREEN_H-12);
  textSize(11);textAlign(LEFT,TOP);
  int yB=SCREEN_Y+SCREEN_H+7,colW=SCREEN_W/NUM_CH;
  for(int ch=0;ch<NUM_CH;ch++){
    int xB=SCREEN_X+ch*colW+6;
    noStroke();fill(CH_COLORS[ch]);rect(xB,yB,3,80);xB+=8;
    fill(CH_COLORS[ch]);textSize(11);
    text("CH"+(ch+1)+(active[ch]?"":" [OFF]"),xB,yB);
    if(active[ch]){
      float[] m=measures[ch];float half=(colW-20)/2.0;
      fill(C_TEXT_MAIN);textSize(9.5);
      text("Vmax: "+nf(m[0],1,3)+"V",xB,yB+13);
      text("Vmin: "+nf(m[1],1,3)+"V",xB,yB+25);
      text("Vrms: "+nf(m[3],1,3)+"V",xB+half,yB+13);
      fill(CH_COLORS[ch]);text("Vpp:  "+nf(m[2],1,3)+"V",xB+half,yB+25);
      fill(C_TEXT_ACCENT);text("Freq: "+(m[4]>0?nf(m[4],1,2)+"Hz":"---"),xB,yB+37);
      fill(C_TEXT_DIM);text("T: "+(m[5]>0?nf(m[5],1,2)+"ms":"---"),xB+half,yB+37);
      noStroke();fill(C_CHASSIS_LT);rect(xB,yB+50,colW-22,4,2);
      fill(CH_COLORS[ch]);rect(xB,yB+50,constrain(map(m[2],0,6,0,colW-22),0,colW-22),4,2);
      String[] fn={"Aucun","LP","Médian","Moy."};
      color[] fc={C_TEXT_DIM,color(20,158,198),color(198,98,18),color(98,198,78)};
      fill(fc[filterMode[ch]]);textSize(9);text("▸ "+fn[filterMode[ch]],xB,yB+58);
    } else {
      fill(C_TEXT_DIM);textSize(9.5);text("— désactivé —",xB,yB+30);
    }
    stroke(C_PANEL_BORDER);strokeWeight(1);
    if(ch<NUM_CH-1) line(SCREEN_X+(ch+1)*colW,yB,SCREEN_X+(ch+1)*colW,yB+70);
    noStroke();
  }
  if(showCursors){
    fill(C_TEXT_ACCENT);textSize(10);
    text("Δt="+nf(cur_dt,1,2)+"ms",SCREEN_X+4,yB+72);
    text("Δf="+(cur_df>0?nf(cur_df,1,1)+"Hz":"---"),SCREEN_X+112,yB+72);
    fill(color(52,220,190));
    text("ΔV="+nf(cur_dv,1,3)+"V",SCREEN_X+245,yB+72);
    text("Y1="+nf(cur_v1,1,3)+"V",SCREEN_X+365,yB+72);
    text("Y2="+nf(cur_v2,1,3)+"V",SCREEN_X+478,yB+72);
  }
}

// ═══════════════════════════════════════════════════════════════════════════
//  PANNEAU DROIT
// ═══════════════════════════════════════════════════════════════════════════
void drawRightPanel(){
  int x=PANEL_X,w=PANEL_W_CST;
  noStroke();fill(C_PANEL_BG);rect(x,0,w,height);
  // Logo EPT miniature (toujours disponible)
  imageMode(CENTER);
  image(gLogo,x+w-38,40,62,62);
  imageMode(CORNER);
  fill(C_TEXT_ACCENT);textSize(13);textAlign(LEFT,TOP);
  text("TEKLAB 4000",x+10,12);
  fill(C_TEXT_DIM);textSize(8);
  text("OSCILLOSCOPE NUMÉRIQUE 4 VOIES  v8.0",x+10,28);
  stroke(C_PANEL_BORDER);strokeWeight(1);line(x+8,46,x+w-8,46);noStroke();
  int[] cY={51,188,325,462};
  String[] cL={"CANAL 1","CANAL 2","CANAL 3","CANAL 4"};
  for(int i=0;i<NUM_CH;i++) drawChannelFrame(x+4,cY[i],w-8,128,cL[i],CH_COLORS[i],i);
  drawSectionFrame(x+4,603,w-8,58,"DÉCLENCHEUR",C_BTN_WARN);
  drawSectionFrame(x+4,668,w-8,212,"ACQUISITION & EXPORT",C_BTN_BLUE);
  textAlign(LEFT,BASELINE);
}

void drawChannelFrame(int x,int y,int w,int h,String lbl,color c,int ch){
  noStroke();fill(C_CHASSIS);rect(x,y,w,h,6);
  stroke(c,active[ch]?190:50);strokeWeight(1.5);noFill();rect(x,y,w,h,6);
  noStroke();fill(c,active[ch]?25:8);rect(x+1,y+1,w-2,20,5,5,0,0);
  fill(c,active[ch]?255:110);textSize(10);textAlign(RIGHT,TOP);
  text(lbl,x+w-6,y+4);textAlign(LEFT,BASELINE);noStroke();
}
void drawSectionFrame(int x,int y,int w,int h,String lbl,color c){
  noStroke();fill(C_CHASSIS);rect(x,y,w,h,6);
  stroke(c,108);strokeWeight(1);noFill();rect(x,y,w,h,6);
  fill(C_TEXT_DIM);textSize(8);textAlign(RIGHT,TOP);
  text(lbl,x+w-6,y+4);textAlign(LEFT,BASELINE);
}

// ═══════════════════════════════════════════════════════════════════════════
//  BARRE D'ÉTAT
// ═══════════════════════════════════════════════════════════════════════════
void drawStatusBar(){
  int yBar=height-24;noStroke();
  fill(darkMode?color(10,12,16):color(190,198,208));rect(0,yBar,SCREEN_W+SCREEN_X*2,24);
  textSize(10);textAlign(LEFT,CENTER);
  for(int i=0;i<NUM_CH;i++){
    fill(CH_COLORS[i]);
    text("CH"+(i+1)+" "+(active[i]?nf(TENSION_BASE/gain[i],1,2)+"V/d":"OFF"),SCREEN_X+i*200,yBar+12);
  }
  fill(C_TEXT_ACCENT);text("TIME ×"+baseTemps,SCREEN_X+810,yBar+12);
  fill(C_TEXT_DIM);text("ZOOM "+nf(zoomX,1,2)+"×",SCREEN_X+880,yBar+12);
  if(trigEnabled){fill(trigArmed?C_BTN_WARN:C_BTN_RUN);text("TRIG CH"+(trigCh+1)+(trigRising?"▲":"▼")+(trigArmed?" ARMÉ":" DÉCL."),SCREEN_X+955,yBar+12);}
  fill(C_TEXT_DIM);textAlign(RIGHT,CENTER);
  // Affiche le débit mesuré en temps réel (SPS) et la vitesse série
  String rateStr = measuredSPS > 0 ? nf(measuredSPS,0,0)+" SPS" : "---";
  text("EPT v8.0  |  "+(darkMode?"● SOMBRE":"○ CLAIR")+"  |  "
       +(monPort!=null?"COM8 @ "+BAUD_RATE:"DÉMO")
       +"  |  "+rateStr
       +"  |  "+nf(frameRate,0,0)+" fps  |  F=fullscreen  T=thème",
       SCREEN_X+SCREEN_W,yBar+12);
  textAlign(LEFT,BASELINE);
}

// ═══════════════════════════════════════════════════════════════════════════
//  THÈME
// ═══════════════════════════════════════════════════════════════════════════
void applyTheme(){
  if(darkMode){
    C_APP_BG=color(12,14,18);C_CHASSIS=color(22,26,32);C_CHASSIS_LT=color(36,42,50);
    C_SCREEN_BG=color(3,8,5);C_GRID_FINE=color(12,28,15);C_GRID_MED=color(22,50,28);
    C_GRID_CENTER=color(52,105,60);C_PANEL_BG=color(20,24,30);C_PANEL_BORDER=color(42,50,60);
    C_TEXT_MAIN=color(205,218,210);C_TEXT_DIM=color(90,108,98);C_TEXT_ACCENT=color(255,195,45);
    C_BTN_RUN=color(35,185,55);C_BTN_STOP=color(195,45,38);C_BTN_WARN=color(225,155,18);
    C_BTN_BLUE=color(18,115,195);C_BTN_PURPLE=color(135,45,205);
    C_KNOB_RING=color(72,84,98);C_KNOB_CTR=color(40,48,58);C_BEZEL=color(18,22,28);
  } else {
    C_APP_BG=color(232,236,242);C_CHASSIS=color(212,218,228);C_CHASSIS_LT=color(195,204,216);
    C_SCREEN_BG=color(245,250,255);C_GRID_FINE=color(195,212,225);C_GRID_MED=color(165,188,208);
    C_GRID_CENTER=color(120,155,182);C_PANEL_BG=color(225,230,238);C_PANEL_BORDER=color(180,192,208);
    C_TEXT_MAIN=color(25,35,52);C_TEXT_DIM=color(95,112,132);C_TEXT_ACCENT=color(175,95,8);
    C_BTN_RUN=color(22,148,42);C_BTN_STOP=color(175,32,25);C_BTN_WARN=color(195,125,8);
    C_BTN_BLUE=color(12,92,172);C_BTN_PURPLE=color(108,28,182);
    C_KNOB_RING=color(145,162,182);C_KNOB_CTR=color(208,216,228);C_BEZEL=color(192,200,212);
  }
}

// ═══════════════════════════════════════════════════════════════════════════
//  UI ControlP5
// ═══════════════════════════════════════════════════════════════════════════
void buildUI(){
  int px=PANEL_X+8;
  cp5.addToggle("powerOn").setPosition(px,12).setSize(44,20).setValue(true).setLabel("POWER")
     .setColorActive(color(36,172,36)).setColorBackground(color(172,36,36))
     .getCaptionLabel().align(ControlP5.CENTER,ControlP5.CENTER).setColor(255);
  cp5.addToggle("runOscillo").setPosition(px+52,12).setSize(52,20).setValue(true).setLabel("RUN/STOP")
     .setColorActive(C_BTN_RUN).setColorBackground(C_BTN_STOP)
     .getCaptionLabel().align(ControlP5.CENTER,ControlP5.CENTER).setColor(255);
  cp5.addButton("autoScale").setPosition(px+112,12).setSize(54,20).setLabel("AUTO SET")
     .setColorBackground(C_BTN_WARN).setColorActive(color(255,212,52))
     .setColorCaptionLabel(color(0)).getCaptionLabel().align(ControlP5.CENTER,ControlP5.CENTER);
  cp5.addButton("captureScreen").setPosition(px+174,12).setSize(62,20).setLabel("CAPTURE PNG")
     .setColorBackground(C_BTN_BLUE).setColorActive(color(0,162,212))
     .getCaptionLabel().align(ControlP5.CENTER,ControlP5.CENTER);

  String[][] names={
    {"amplitudeCH1","freqCH1","posYCH1","invCH1","activeCH1","calcPolyCH1","filterModeCH1","filterCutCH1"},
    {"amplitudeCH2","freqCH2","posYCH2","invCH2","activeCH2","calcPolyCH2","filterModeCH2","filterCutCH2"},
    {"amplitudeCH3","freqCH3","posYCH3","invCH3","activeCH3","calcPolyCH3","filterModeCH3","filterCutCH3"},
    {"amplitudeCH4","freqCH4","posYCH4","invCH4","activeCH4","calcPolyCH4","filterModeCH4","filterCutCH4"}
  };
  int[] chY={51,188,325,462};
  for(int i=0;i<NUM_CH;i++) buildChannelUI(names[i],px,chY[i]+22,CH_COLORS[i]);

  int ty=608;
  cp5.addToggle("trigEnabled").setPosition(px,ty).setSize(50,20).setValue(false).setLabel("TRIG ON")
     .setColorActive(C_BTN_WARN).setColorBackground(color(86))
     .getCaptionLabel().align(ControlP5.CENTER,ControlP5.CENTER).setColor(0);
  cp5.addToggle("trigRising").setPosition(px+58,ty).setSize(50,20).setValue(true).setLabel("▲ / ▼")
     .setColorActive(color(52,182,255)).setColorBackground(color(86))
     .getCaptionLabel().align(ControlP5.CENTER,ControlP5.CENTER).setColor(0);
  cp5.addKnob("trigChannel").setPosition(px+116,ty-8).setRadius(13).setRange(1,4).setValue(1)
     .setLabel("CH").setNumberOfTickMarks(3)
     .setColorActive(C_BTN_WARN).setColorForeground(color(96)).setColorBackground(C_KNOB_CTR)
     .setColorCaptionLabel(C_TEXT_DIM).setColorValueLabel(C_TEXT_MAIN);
  cp5.addKnob("trigLevelKnob").setPosition(px+185,ty-8).setRadius(13).setRange(-250,250).setValue(0)
     .setLabel("LVL").setColorActive(C_BTN_WARN)
     .setColorForeground(color(96)).setColorBackground(C_KNOB_CTR).setDragDirection(Knob.VERTICAL)
     .setColorCaptionLabel(C_TEXT_DIM).setColorValueLabel(C_TEXT_MAIN);

  int cy=674;
  cp5.addToggle("showCursors").setPosition(px,cy).setSize(56,20).setValue(false).setLabel("CURSEURS")
     .setColorActive(color(192,192,0)).setColorBackground(color(76))
     .getCaptionLabel().align(ControlP5.CENTER,ControlP5.CENTER).setColor(0);
  cp5.addToggle("showFFT").setPosition(px+64,cy).setSize(56,20).setValue(false).setLabel("FFT VIEW")
     .setColorActive(C_BTN_PURPLE).setColorBackground(color(76))
     .getCaptionLabel().align(ControlP5.CENTER,ControlP5.CENTER).setColor(255);

  int by=700;
  cp5.addKnob("baseTemps").setPosition(px,by).setRadius(18).setRange(1,10).setValue(2)
     .setLabel("TEMPS").setColorForeground(C_KNOB_RING).setColorActive(color(76))
     .setColorBackground(C_KNOB_CTR).setDragDirection(Knob.VERTICAL)
     .setColorCaptionLabel(C_TEXT_DIM).setColorValueLabel(C_TEXT_MAIN);
  cp5.addButton("toggleTheme").setPosition(px+46,by).setSize(106,20).setLabel("THÈME ●/○  (T)")
     .setColorBackground(color(52,52,72)).setColorActive(color(98,98,138))
     .getCaptionLabel().align(ControlP5.CENTER,ControlP5.CENTER);
  cp5.addButton("toggleFullscreen").setPosition(px+160,by).setSize(96,20).setLabel("PLEIN ÉCRAN (F)")
     .setColorBackground(color(38,52,68)).setColorActive(color(78,108,138))
     .getCaptionLabel().align(ControlP5.CENTER,ControlP5.CENTER);
  cp5.addButton("printMath").setPosition(px+46,by+28).setSize(210,18).setLabel("IMPRIMER MATH (CONSOLE)")
     .setColorBackground(color(26,66,155)).setColorActive(color(66,115,232))
     .getCaptionLabel().align(ControlP5.CENTER,ControlP5.CENTER);
  cp5.addButton("exportAscii").setPosition(px+46,by+52).setSize(210,18).setLabel("EXPORTER FICHIER DONNÉES")
     .setColorBackground(color(105,26,155)).setColorActive(color(165,76,232))
     .getCaptionLabel().align(ControlP5.CENTER,ControlP5.CENTER);
  cp5.addButton("resetZoom").setPosition(px+46,by+76).setSize(100,18).setLabel("RESET ZOOM")
     .setColorBackground(color(36,66,40)).setColorActive(color(72,135,82))
     .getCaptionLabel().align(ControlP5.CENTER,ControlP5.CENTER);
  cp5.addButton("resetFilters").setPosition(px+154,by+76).setSize(102,18).setLabel("RESET FILTRES")
     .setColorBackground(color(78,36,14)).setColorActive(color(158,82,28))
     .getCaptionLabel().align(ControlP5.CENTER,ControlP5.CENTER);
}

void buildChannelUI(String[] n,int x,int y,color c){
  int r=14;color cV=C_TEXT_MAIN,cC=C_TEXT_DIM;
  cp5.addKnob(n[0]).setPosition(x,y).setRadius(r).setRange(0.1,5.0).setValue(1.0).setLabel("AMP")
     .setColorActive(c).setColorForeground(C_KNOB_RING).setColorBackground(C_KNOB_CTR)
     .setNumberOfTickMarks(10).setTickMarkLength(3).setDragDirection(Knob.VERTICAL)
     .setColorValueLabel(cV).setColorCaptionLabel(cC);
  cp5.addKnob(n[1]).setPosition(x+40,y).setRadius(r).setRange(0.2,5.0).setValue(1.0).setLabel("ZOOM")
     .setColorActive(c).setColorForeground(C_KNOB_RING).setColorBackground(C_KNOB_CTR)
     .setNumberOfTickMarks(10).setTickMarkLength(3).setDragDirection(Knob.VERTICAL)
     .setColorValueLabel(cV).setColorCaptionLabel(cC);
  cp5.addKnob(n[2]).setPosition(x+80,y).setRadius(r).setRange(-250,250).setValue(0).setLabel("Y-POS")
     .setColorActive(c).setColorForeground(C_KNOB_RING).setColorBackground(C_KNOB_CTR)
     .setNumberOfTickMarks(0).setDragDirection(Knob.VERTICAL)
     .setColorValueLabel(cV).setColorCaptionLabel(cC);
  int bx=x+122,bh=20;
  cp5.addToggle(n[4]).setPosition(bx,y+6).setSize(28,bh).setValue(true).setLabel("ON")
     .setColorActive(c).setColorBackground(color(66))
     .getCaptionLabel().align(ControlP5.CENTER,ControlP5.CENTER).setColor(255);
  cp5.addToggle(n[3]).setPosition(bx+34,y+6).setSize(28,bh).setLabel("INV")
     .setColorActive(c).setColorBackground(color(66))
     .getCaptionLabel().align(ControlP5.CENTER,ControlP5.CENTER).setColor(255);
  cp5.addToggle(n[5]).setPosition(bx+68,y+6).setSize(34,bh).setLabel("MATH")
     .setColorActive(c).setColorBackground(color(66))
     .getCaptionLabel().align(ControlP5.CENTER,ControlP5.CENTER).setColor(255);
  cp5.addScrollableList(n[6]).setPosition(x,y+42).setSize(112,62)
     .setBarHeight(16).setItemHeight(15)
     .addItem("Aucun filtre",0).addItem("Passe-bas LP",1)
     .addItem("Médian",2).addItem("Moy. glissante",3)
     .setLabel("FILTRE").setColorBackground(color(26,32,40))
     .setColorActive(c).setColorCaptionLabel(cC).setColorValueLabel(cV).close();
  cp5.addKnob(n[7]).setPosition(x+120,y+44).setRadius(13).setRange(0.01,0.499).setValue(0.1)
     .setLabel("FC/W").setColorActive(c)
     .setColorForeground(C_KNOB_RING).setColorBackground(C_KNOB_CTR).setDragDirection(Knob.VERTICAL)
     .setColorValueLabel(cV).setColorCaptionLabel(cC);
}

// ═══════════════════════════════════════════════════════════════════════════
//  TRIGGER
// ═══════════════════════════════════════════════════════════════════════════
void searchTrigger(){
  float tLvlRaw=map(trigLevel,0,SCREEN_H,4095,0),hyster=55;
  for(int i=10;i<BUFFER_SIZE-1;i++){
    float prev=rawHist[trigCh][i-1],curr=rawHist[trigCh][i];
    boolean f=trigRising?(prev<tLvlRaw-hyster&&curr>=tLvlRaw):(prev>tLvlRaw+hyster&&curr<=tLvlRaw);
    if(f){trigPos=i;trigArmed=false;thread("rearmTrigger");break;}
  }
}
void rearmTrigger(){delay(200);trigArmed=true;}

// ═══════════════════════════════════════════════════════════════════════════
//  AUTO SCALE
// ═══════════════════════════════════════════════════════════════════════════
void doAutoScale(){
  baseTemps=2;cp5.getController("baseTemps").setValue(2);
  cp5.getController("showFFT").setValue(0);
  zoomX=1.0;panOffsetX=0;
  String[][] ns={{"amplitudeCH1","freqCH1","posYCH1","invCH1"},{"amplitudeCH2","freqCH2","posYCH2","invCH2"},
    {"amplitudeCH3","freqCH3","posYCH3","invCH3"},{"amplitudeCH4","freqCH4","posYCH4","invCH4"}};
  for(int i=0;i<NUM_CH;i++){
    cp5.getController(ns[i][0]).setValue(1);cp5.getController(ns[i][1]).setValue(1);
    cp5.getController(ns[i][2]).setValue(0);cp5.getController(ns[i][3]).setValue(0);
  }
  if(!runOscillo){runOscillo=true;cp5.getController("runOscillo").setValue(1);}
  invalidateAllCaches();
}

// ═══════════════════════════════════════════════════════════════════════════
//  INTERPOLATION DES COURBES AFFICHÉES
//  • Linéaire  : valeur entre deux samples consécutifs
//  • Spline cubique de Catmull-Rom : lissage entre 4 points
// ═══════════════════════════════════════════════════════════════════════════

// Interpolation linéaire entre deux points du signal à position fractionnaire px
float interpLinear(float[] sig, float px){
  int i0 = constrain((int)px, 0, sig.length-2);
  float t = px - i0;
  return sig[i0]*(1-t) + sig[i0+1]*t;
}

// Interpolation Catmull-Rom (spline cubique) — plus douce que linéaire
float interpCatmullRom(float[] sig, float px){
  int i1 = constrain((int)px, 0, sig.length-1);
  int i0 = max(i1-1, 0);
  int i2 = min(i1+1, sig.length-1);
  int i3 = min(i1+2, sig.length-1);
  float t = px - (int)px;
  float p0=sig[i0], p1=sig[i1], p2=sig[i2], p3=sig[i3];
  return 0.5*((2*p1) + (-p0+p2)*t + (2*p0-5*p1+4*p2-p3)*t*t + (-p0+3*p1-3*p2+p3)*t*t*t);
}

// Génère un tableau de N points interpolés (Catmull-Rom) sur le signal affiché
// Convertit en tension (V) avec les paramètres du canal
float[] getInterpolatedCurve(int ch, int N){
  float[] sig = getProcessedSignal(ch);
  float[] out = new float[N];
  float rz=SCREEN_H/2.0-posY[ch], vppx=TENSION_BASE/50.0/gain[ch];
  for(int i=0;i<N;i++){
    float px = map(i, 0, N-1, 0, SCREEN_W-1);
    float yPx = interpCatmullRom(sig, px);
    out[i] = (rz - yPx) * vppx;  // conversion pixel → tension (V)
  }
  return out;
}
String getPolyString(int ch,float[] signal){
  int deg=5,n=deg+1,step=80,startX=200;
  double[] xArr=new double[n],yArr=new double[n];
  float rz=SCREEN_H/2.0-posY[ch];
  for(int i=0;i<n;i++){int px=startX+i*step;xArr[i]=(px-startX)/(double)(deg*step);yArr[i]=rz-signal[constrain(px,0,SCREEN_W-1)];}
  double[] c=dividedDifferences(xArr,yArr,n);
  StringBuilder p=new StringBuilder("P(x) = ");
  for(int i=0;i<n;i++){
    if(i>0)p.append(c[i]>=0?" + ":" - ");
    p.append(nf(abs((float)c[i]),1,4));
    for(int j=0;j<i;j++) p.append(xArr[j]==0?"·x":"·(x-"+nf((float)xArr[j],1,4)+")");
  }
  return p.toString();
}
double[] dividedDifferences(double[] x,double[] y,int n){
  double[][] f=new double[n][n];
  for(int i=0;i<n;i++) f[i][0]=y[i];
  for(int j=1;j<n;j++) for(int i=j;i<n;i++) f[i][j]=(f[i][j-1]-f[i-1][j-1])/(x[i]-x[i-j]);
  double[] c=new double[n];for(int i=0;i<n;i++) c[i]=f[i][i];return c;
}

// ═══════════════════════════════════════════════════════════════════════════
//  EXPORT
// ═══════════════════════════════════════════════════════════════════════════
void imprimerCompteRenduPoly(){
  println("\n╔══════════════════════════════════════════════════════╗");
  println("║  COMPTE RENDU — EPT TEKLAB 4000 v8.0                ║");
  println("╚══════════════════════════════════════════════════════╝");
  String[] fn={"Aucun","Butterworth LP","Médian","Moy. glissante"};
  boolean any=false;
  for(int ch=0;ch<NUM_CH;ch++){
    if(!active[ch]||!math[ch]) continue;any=true;
    float[] s=getProcessedSignal(ch),m=computeMeasures(ch,s);
    println("─── CANAL "+(ch+1)+"  Filtre: "+fn[filterMode[ch]]);
    println("  Vmax: "+nf(m[0],1,4)+"V  Vmin: "+nf(m[1],1,4)+"V  Vpp: "+nf(m[2],1,4)+"V  Vrms: "+nf(m[3],1,4)+"V");
    println("  Fréq: "+(m[4]>0?nf(m[4],1,3)+"Hz":"—")+"  Période: "+(m[5]>0?nf(m[5],1,3)+"ms":"—"));
    println("  Poly: "+getPolyString(ch,s));
    // Interpolation Catmull-Rom sur 20 points régulièrement espacés
    float[] interp = getInterpolatedCurve(ch, 20);
    StringBuilder sb = new StringBuilder("  Interp (Catmull-Rom, 20pts) [V]: ");
    for(int i=0;i<interp.length;i++){ sb.append(nf(interp[i],1,4)); if(i<interp.length-1) sb.append(", "); }
    println(sb.toString());
  }
  if(!any) println("  Aucun canal n'a MATH activé.");
  println("══════════════════════════════════════════════════════\n");
}

void exporterCompteRenduAscii(){
  PrintWriter out=createWriter("compte_rendu_teklab4000.txt");
  out.println("════════════════════════════════════════════════════════════════");
  out.println("       COMPTE RENDU — EPT TEKLAB 4000 v8.0");
  out.println("════════════════════════════════════════════════════════════════");
  out.println("  Date: "+day()+"/"+month()+"/"+year()+"  "+nf(hour(),2)+":"+nf(minute(),2)+":"+nf(second(),2));
  out.println("  Mode: "+(showFFT?"FFT":"Temporel")+"  Zoom: ×"+nf(zoomX,1,2)
    +"  USB: "+(monPort!=null?"COM8 @ "+BAUD_RATE+" bps":"Démo")
    +"  SPS: "+nf(measuredSPS,0,0));
  out.println();
  String[] fn={"Aucun","Butterworth LP 2ème ordre","Médian","Moy. glissante"};
  for(int ch=0;ch<NUM_CH;ch++){
    out.println("┌─ CANAL "+(ch+1)+" "+(active[ch]?"[ACTIF]":"[INACTIF]")+" "+"─".repeat(44));
    out.println("│  Gain: ×"+nf(gain[ch],1,2)+"  Zoom: ×"+nf(fzoom[ch],1,2)+"  PosY: "+posY[ch]+"px  Inv: "+(inv[ch]?"OUI":"NON"));
    out.println("│  Filtre: "+fn[filterMode[ch]]);
    if(active[ch]){
      float[] s=getProcessedSignal(ch),m=computeMeasures(ch,s);
      out.println("│  Vmax: "+nf(m[0],1,4)+"V  Vmin: "+nf(m[1],1,4)+"V  Vpp: "+nf(m[2],1,4)+"V  Vrms: "+nf(m[3],1,4)+"V");
      out.println("│  Fréq: "+(m[4]>0?nf(m[4],1,3)+"Hz":"—")+"  Période: "+(m[5]>0?nf(m[5],1,3)+"ms":"—"));
      if(math[ch]) out.println("│  Poly: "+getPolyString(ch,s));
      // ── Interpolation Catmull-Rom (50 points sur la fenêtre affichée) ────────
      float[] interp = getInterpolatedCurve(ch, 50);
      float ez=fzoom[ch]*zoomX;
      float secPerPx = (SCREEN_W/ez)/(SCREEN_W*SAMPLE_RATE);
      out.println("│  ── Interpolation Catmull-Rom (50 points, fenêtre affichée) ──");
      out.println("│  Pas temporel entre points : "+nf(secPerPx*(SCREEN_W-1)/49*1000,1,4)+" ms");
      StringBuilder row = new StringBuilder("│  t(ms) → V(V) :");
      for(int i=0;i<interp.length;i++){
        float tMs = secPerPx * map(i,0,interp.length-1,0,SCREEN_W-1) * 1000;
        if(i%10==0){ out.println(row.toString()); row=new StringBuilder("│    "); }
        row.append("("+nf(tMs,1,2)+","+nf(interp[i],1,4)+") ");
      }
      out.println(row.toString());
      // Interpolation linéaire — valeurs aux 10 points clés
      out.println("│  ── Interpolation linéaire (10 points clés) ──────────────────");
      float[] lin10 = getInterpolatedCurve(ch, 10);
      StringBuilder linRow = new StringBuilder("│  ");
      for(int i=0;i<lin10.length;i++){
        float tMs = secPerPx * map(i,0,lin10.length-1,0,SCREEN_W-1) * 1000;
        linRow.append("("+nf(tMs,1,2)+"ms, "+nf(lin10[i],1,4)+"V)");
        if(i<lin10.length-1) linRow.append("  ");
      }
      out.println(linRow.toString());
    }
    out.println("└"+"─".repeat(52));
  }
  out.flush();out.close();
  println("[OK] Export : compte_rendu_teklab4000.txt");
}

void captureScreen(){
  String f="capture_teklab4000_"+year()+nf(month(),2)+nf(day(),2)+"_"+nf(hour(),2)+nf(minute(),2)+nf(second(),2)+".png";
  save(f);println("[OK] Capture : "+f);
}

void resetAllBuffers(){
  for(int i=0;i<NUM_CH;i++){
    for(int j=0;j<BUFFER_SIZE;j++) rawHist[i][j]=2048;
    ringHead[i]=0;
    chSampleCount[i]=0;
    bwX1[i][0]=bwX2[i][0]=bwY1[i][0]=bwY2[i][0]=0;
  }
  globalSampleCount=0;
  rateCountSamples=0;
  measuredSPS=0;
  demoInit=false;         // force le pré-remplissage démo au prochain appel
  demoLastMs=millis();
  rateLastMillis=millis();
  invalidateAllCaches();
}

void resetZoom(){zoomX=1.0;panOffsetX=0;invalidateAllCaches();}
void resetFilters(){
  for(int i=0;i<NUM_CH;i++){filterMode[i]=0;filterCutoff[i]=0.1;bwX1[i][0]=bwX2[i][0]=bwY1[i][0]=bwY2[i][0]=0;bwFcLast[i]=-1;}
  invalidateAllCaches();
}

// ═══════════════════════════════════════════════════════════════════════════
//  PLEIN ÉCRAN & THÈME
// ═══════════════════════════════════════════════════════════════════════════
void doToggleFullscreen(){
  isFullscreen=!isFullscreen;
  surface.setResizable(true);
  if(isFullscreen) surface.setSize(displayWidth,displayHeight);
  else             surface.setSize(BASE_W,BASE_H);
  // Attendre que Processing ait effectivement redimensionné la fenêtre
  // avant de reconstruire les PGraphics (évite le blocage)
  thread("rebuildGraphicsDeferred");
}

// Exécuté en thread séparé : attend 120 ms puis reconstruit tous les PGraphics
// au bon format — évite le gel causé par createGraphics() pendant le resize
void rebuildGraphicsDeferred(){
  delay(120);
  // Reconstruire gScreen à la bonne taille (SCREEN_W × SCREEN_H sont finaux,
  // mais gBezel/gGrid dépendent du rendu courant)
  gScreen = createGraphics(SCREEN_W, SCREEN_H);
  buildBezel();
  buildGrid();
  invalidateAllCaches();
}
void doToggleTheme(){
  darkMode=!darkMode;
  applyTheme();
  buildBezel();buildGrid();buildLogoEPT();
  invalidateAllCaches();
}

// ═══════════════════════════════════════════════════════════════════════════
//  PORT SÉRIE — Parser robuste 921600 bps
//  • Reconstruit les trames même si elles arrivent fragmentées
//  • Valide le format CSV strict : exactement 4 entiers 0-4095
//  • Auto-mesure SAMPLE_RATE toutes les RATE_WINDOW_MS ms
// ═══════════════════════════════════════════════════════════════════════════
void serialEvent(Serial p){
  if(!runOscillo||!powerOn) return;

  // ── Drainer tout ce qui est disponible dans le buffer matériel ────────────
  while(p.available() > 0){
    int c = p.read();
    if(c < 0) break;

    if(c == '\n' || c == '\r'){
      // Fin de trame — parser la ligne accumulée
      String line = serialBuf.toString().trim();
      serialBuf.setLength(0);           // vider pour la prochaine trame

      if(line.length() == 0) continue;

      // ── Valider et décoder CSV "v1,v2,v3,v4" ────────────────────────────
      String[] tok = split(line, ',');
      if(tok.length != 4) continue;     // trame incomplète ou corrompue

      float[] v = new float[4];
      boolean valid = true;
      for(int i=0;i<4;i++){
        try {
          v[i] = Integer.parseInt(tok[i].trim());
          if(v[i] < 0 || v[i] > 4095){ valid=false; break; }
        } catch(Exception ex){ valid=false; break; }
      }
      if(!valid) continue;              // rejeter trame hors plage ADC

      // ── Injecter dans le ring buffer ─────────────────────────────────────
      for(int i=0;i<NUM_CH;i++){
        if(active[i]){
          rawHist[i][ringHead[i]] = v[i];
          ringHead[i] = (ringHead[i]+1) % BUFFER_SIZE;
          chSampleCount[i]++;
          invalidateCache(i);
        }
      }
      globalSampleCount++;
      rateCountSamples++;
      if(trigEnabled&&trigArmed) searchTrigger();

    } else {
      // Accumuler les caractères de la trame (protection overflow)
      if(serialBuf.length() < 64) serialBuf.append((char)c);
      else serialBuf.setLength(0);      // trame trop longue → flush (glitch)
    }
  }

  // ── Auto-mesure SAMPLE_RATE ──────────────────────────────────────────────
  long now = millis();
  long elapsed = now - rateLastMillis;
  if(elapsed >= RATE_WINDOW_MS && rateCountSamples > 0){
    measuredSPS   = rateCountSamples * 1000.0 / elapsed;
    SAMPLE_RATE   = measuredSPS;        // calibration dynamique
    rateCountSamples = 0;
    rateLastMillis   = now;
  }
}

// ═══════════════════════════════════════════════════════════════════════════
//  SOURIS
// ═══════════════════════════════════════════════════════════════════════════
boolean onScreen(){return mouseX>=SCREEN_X&&mouseX<SCREEN_X+SCREEN_W&&mouseY>=SCREEN_Y&&mouseY<SCREEN_Y+SCREEN_H;}
float mX(){return mouseX-SCREEN_X;}
float mY(){return mouseY-SCREEN_Y;}

void mouseWheel(MouseEvent e){
  if(!onScreen()||showCursors) return;
  float delta=e.getCount();float prevZ=zoomX;
  zoomX=constrain(zoomX*(delta<0?1.15:0.87),0.12,20.0);
  float cx=mX()/SCREEN_W;
  panOffsetX+=(SCREEN_W/prevZ-SCREEN_W/zoomX)*cx;
  invalidateAllCaches();
}

void mousePressed(){
  if(!onScreen()) return;
  float mx=mX(),my=mY();
  if(showCursors&&mouseButton==LEFT){
    float tol=10;
    if(abs(mx-cx1)<tol){dragCursor=0;return;}
    if(abs(mx-cx2)<tol){dragCursor=1;return;}
    if(abs(my-cy1)<tol){dragCursor=2;return;}
    if(abs(my-cy2)<tol){dragCursor=3;return;}
  }
  if(!showCursors&&(mouseButton==CENTER||mouseButton==RIGHT)){
    isPanning=true;panStartX=mouseX;panStartOff=panOffsetX;
  }
}

void mouseDragged(){
  if(dragCursor>=0){
    float mx=constrain(mX(),2,SCREEN_W-2);
    float my=constrain(mY(),2,SCREEN_H-2);
    if(dragCursor==0)      cx1=mx;
    else if(dragCursor==1) cx2=mx;
    else if(dragCursor==2) cy1=my;
    else                   cy2=my;
    return;
  }
  if(isPanning){
    panOffsetX=panStartOff-(mouseX-panStartX)*(SCREEN_W/(fzoom[0]*zoomX))/SCREEN_W;
    invalidateAllCaches();
  }
}
void mouseReleased(){dragCursor=-1;isPanning=false;}
void mouseMoved(){
  if(!onScreen()||!showCursors){cursor(ARROW);return;}
  float mx=mX(),my=mY(),tol=10;
  if(abs(mx-cx1)<tol||abs(mx-cx2)<tol||abs(my-cy1)<tol||abs(my-cy2)<tol) cursor(MOVE);
  else cursor(CROSS);
}

// ═══════════════════════════════════════════════════════════════════════════
//  CLAVIER
// ═══════════════════════════════════════════════════════════════════════════
void keyPressed(){
  if(key=='f'||key=='F') doToggleFullscreen();
  if(key=='t'||key=='T') doToggleTheme();
  if(key==' '){runOscillo=!runOscillo;if(cp5!=null)cp5.getController("runOscillo").setValue(runOscillo?1:0);}
  if(key=='r'||key=='R') resetZoom();
  if(key=='a'||key=='A') doAutoScale();
}

// ═══════════════════════════════════════════════════════════════════════════
//  ÉVÉNEMENTS ControlP5
// ═══════════════════════════════════════════════════════════════════════════
void controlEvent(ControlEvent e){
  if(!e.isController()) return;
  String n=e.getController().getName();float v=e.getController().getValue();
  switch(n){
    case "amplitudeCH1":gain[0]=v;invalidateCache(0);break;
    case "freqCH1":fzoom[0]=v;invalidateCache(0);break;
    case "posYCH1":posY[0]=v;invalidateCache(0);break;
    case "invCH1":inv[0]=(v==1);invalidateCache(0);break;
    case "activeCH1":
      active[0]=(v==1);
      if(!active[0]){ for(int j=0;j<BUFFER_SIZE;j++) rawHist[0][j]=2048; ringHead[0]=0; chSampleCount[0]=0; }
      invalidateCache(0); break;
    case "calcPolyCH1":math[0]=(v==1);break;
    case "filterModeCH1":setFM(0,(int)v);break;
    case "filterCutCH1":setFC(0,v);break;
    case "amplitudeCH2":gain[1]=v;invalidateCache(1);break;
    case "freqCH2":fzoom[1]=v;invalidateCache(1);break;
    case "posYCH2":posY[1]=v;invalidateCache(1);break;
    case "invCH2":inv[1]=(v==1);invalidateCache(1);break;
    case "activeCH2":
      active[1]=(v==1);
      if(!active[1]){ for(int j=0;j<BUFFER_SIZE;j++) rawHist[1][j]=2048; ringHead[1]=0; chSampleCount[1]=0; }
      invalidateCache(1); break;
    case "calcPolyCH2":math[1]=(v==1);break;
    case "filterModeCH2":setFM(1,(int)v);break;
    case "filterCutCH2":setFC(1,v);break;
    case "amplitudeCH3":gain[2]=v;invalidateCache(2);break;
    case "freqCH3":fzoom[2]=v;invalidateCache(2);break;
    case "posYCH3":posY[2]=v;invalidateCache(2);break;
    case "invCH3":inv[2]=(v==1);invalidateCache(2);break;
    case "activeCH3":
      active[2]=(v==1);
      if(!active[2]){ for(int j=0;j<BUFFER_SIZE;j++) rawHist[2][j]=2048; ringHead[2]=0; chSampleCount[2]=0; }
      invalidateCache(2); break;
    case "calcPolyCH3":math[2]=(v==1);break;
    case "filterModeCH3":setFM(2,(int)v);break;
    case "filterCutCH3":setFC(2,v);break;
    case "amplitudeCH4":gain[3]=v;invalidateCache(3);break;
    case "freqCH4":fzoom[3]=v;invalidateCache(3);break;
    case "posYCH4":posY[3]=v;invalidateCache(3);break;
    case "invCH4":inv[3]=(v==1);invalidateCache(3);break;
    case "activeCH4":
      active[3]=(v==1);
      if(!active[3]){ for(int j=0;j<BUFFER_SIZE;j++) rawHist[3][j]=2048; ringHead[3]=0; chSampleCount[3]=0; }
      invalidateCache(3); break;
    case "calcPolyCH4":math[3]=(v==1);break;
    case "filterModeCH4":setFM(3,(int)v);break;
    case "filterCutCH4":setFC(3,v);break;
    case "baseTemps":baseTemps=(int)v;break;
    case "runOscillo":runOscillo=(v==1);break;
    case "showFFT":showFFT=(v==1);fftDirty=true;break;
    case "powerOn":
      powerOn=(v==1);
      // Vider les buffers au rallumage pour ne pas afficher d'anciennes courbes
      if(powerOn) resetAllBuffers();
      break;
    case "trigEnabled":trigEnabled=(v==1);trigArmed=true;break;
    case "trigRising":trigRising=(v==1);break;
    case "trigChannel":trigCh=(int)v-1;break;
    case "trigLevelKnob":trigLevel=map(v,-250,250,SCREEN_H-80,80);break;
    case "showCursors":
      showCursors=(v==1);
      if(showCursors){runOscillo=false;cp5.getController("runOscillo").setValue(0);}
      else           {runOscillo=true; cp5.getController("runOscillo").setValue(1);}
      break;
    case "autoScale":doAutoScale();break;
    case "printMath":imprimerCompteRenduPoly();break;
    case "exportAscii":exporterCompteRenduAscii();break;
    case "captureScreen":captureScreen();break;
    case "resetZoom":resetZoom();break;
    case "resetFilters":resetFilters();break;
    case "toggleTheme":doToggleTheme();break;
    case "toggleFullscreen":doToggleFullscreen();break;
  }
}

void setFM(int ch,int mode){
  filterMode[ch]=constrain(mode,0,3);
  bwX1[ch][0]=bwX2[ch][0]=bwY1[ch][0]=bwY2[ch][0]=0;
  if(mode==1) computeBwCoeff(ch);
  invalidateCache(ch);
}
void setFC(int ch,float v){
  filterCutoff[ch]=constrain(v,0.01,0.499);
  filterWindow[ch]=constrain((int)(v*20)*2+3,3,51);
  if(filterMode[ch]==1) computeBwCoeff(ch);
  invalidateCache(ch);
}
