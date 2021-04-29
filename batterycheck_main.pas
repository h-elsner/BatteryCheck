{********************************************************}
{                                                        }
{          Batterie Check für Yuneec Kopter              }
{                                                        }
{          Copyright (c) 2021   Helmut Elsner            }
{                                                        }
{       Compiler: FPC 3.2.0  /    Lazarus 2.0.12         }
{                                                        }
{ Pascal programmers tend to plan ahead, they think      }
{ before they type. We type a lot because of Pascal      }
{ verboseness, but usually our code is right from the    }
{ start. We end up typing less because we fix less bugs. }
{           [Jorge Aldo G. de F. Junior]                 }
{********************************************************}

(*
This source is free software; you can redistribute it and/or modify it under
the terms of the GNU General Public License as published by the Free
Software Foundation; either version 2 of the License, or (at your option)
any later version.

This code is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
details.

A copy of the GNU General Public License is available on the World Wide Web
at <http://www.gnu.org/copyleft/gpl.html>. You can also obtain it by writing
to the Free Software Foundation, Inc., 51 Franklin Street - Fifth Floor,
Boston, MA 02110-1335, USA.

================================================================================

Ein Post-Flight Check der benutzen Batterie anhand der FlightLogs
aus dem Controller. Mit Hilfe des Diagramms kann man die Qualität der Batterie abschätzen. Zusätzlich wird in einem Protokoll eine Einschätzung gegeben. Diese ist natürlich nicht verbindlich und mit Vorsicht zu geniessen.

Supported file formats:
- Yuneec telemetry files (.csv) from Q500, typhoon H, H Plus, H3, H920
- Sensor files from Typhoon H Plus, H3
- TLOG files from H520 and other PX4 Autopilot based drones
- Mantis Q/G log files
- Yuneec Breeze log files
- Telemetry files from Blade Chroma and 350QX

*)

unit batterycheck_main;

{$mode objfpc}{$H+}

interface

uses
  Classes, SysUtils, Forms, Controls, Graphics, Dialogs, XMLPropStorage, Menus,
  ExtCtrls, Buttons, ActnList, StdCtrls, TAGraph, TATransformations,
  TAIntervalSources, TATools, TASeries, fileutil, DateUtils, math, LCLIntf,
  ComCtrls;

type

  TMessPkt = record                                  {Messpunkt}
    v: double;                                       {Spannung}
    c: double;                                       {Remaining capacity}
    vmax: double;                                    {Spannungsmaximum}
    vmin: double;                                    {Spannungsminimum}
    nc: integer;                                     {Anzahl Zellen}
    segm: integer;                                   {# Segment des Fluges}
    pid: integer;                                    {Position in discharge curve
                                                      0: Start find max voltage/not charged
                                                      1: Max voltage found, battery charged
                                                      2: Begin discharge
                                                      3: Discharged to threshold}
    t:   TDateTime;                                  {Time stamp}
    td:  TDateTime;                                  {Start discharge}
    tt:  TDateTime;                                  {Threshold reached}
    flt: boolean;                                    {Flight mode detected}
  end;

  { TForm1 }

  TForm1 = class(TForm)
    actOpen: TAction;
    actClose: TAction;
    ActionList1: TActionList;
    btnClose: TBitBtn;
    btnOpen: TBitBtn;
    Chart1: TChart;
    lineUmin: TConstantLine;
    lineVW1: TConstantLine;
    lineVW2: TConstantLine;
    ChartAxisTransformations1AutoScaleAxisTransform1: TAutoScaleAxisTransform;
    ChartAxisTransformations2AutoScaleAxisTransform1: TAutoScaleAxisTransform;
    cbCap: TCheckBox;
    ChartToolset1PanDragTool1: TPanDragTool;
    ChartToolset1ZoomMouseWheelTool1: TZoomMouseWheelTool;
    Panel2: TPanel;
    VSerie: TLineSeries;
    CSerie: TLineSeries;
    ChartAxisTransformations1: TChartAxisTransformations;
    ChartAxisTransformations2: TChartAxisTransformations;
    ChartToolset1: TChartToolset;
    DateTimeIntervalChartSource1: TDateTimeIntervalChartSource;
    ImageList: TImageList;
    MainMenu1: TMainMenu;
    rgBatt: TRadioGroup;
    Splitter: TSplitter;
    txtProtocol: TMemo;
    mnAbout: TMenuItem;
    N2: TMenuItem;
    mnHomePage: TMenuItem;
    mnHelp: TMenuItem;
    mnClose: TMenuItem;
    mnFile: TMenuItem;
    mnLogOpen: TMenuItem;
    mnSave: TMenuItem;
    N1: TMenuItem;
    OpenDialog: TOpenDialog;
    Panel1: TPanel;
    XMLPropStorage1: TXMLPropStorage;
    procedure actCloseExecute(Sender: TObject);
    procedure actOpenExecute(Sender: TObject);
    procedure cbCapClick(Sender: TObject);
    procedure Chart1MouseUp(Sender: TObject; Button: TMouseButton;
      Shift: TShiftState; X, Y: Integer);
    procedure FormCreate(Sender: TObject);
    procedure FormKeyUp(Sender: TObject; var Key: Word; Shift: TShiftState);
    procedure mnAboutClick(Sender: TObject);
    procedure mnHomePageClick(Sender: TObject);
    procedure mnSaveClick(Sender: TObject);
    procedure rgBattClick(Sender: TObject);
  private
    procedure Zeichnen(const fn: string);            {Ein FlightLog auswerten}
    procedure YuneecLegacy(logdat: TMemoryStream; const m: integer);
    procedure BreezeDats(logdat: TMemoryStream);     {Breeze}
    procedure H501Dats(logdat: TMemoryStream);       {Hubsan, mode 9}
    procedure MAVmsg(const logdat: TMemoryStream);     {TLOG, Sensor, Mantis}
    procedure MPanalyse(var m, malt: TMesspkt);      {Kurvenanalyse Spannung}
    procedure Bewertung(mx: TMessPkt; var olist: TStringList; seg: boolean=false);
  public

  end;


var
  Form1: TForm1;
  dbg: Boolean;

const
  meinname='Helmut Elsner';
  email   ='helmut.elsner@live.com';               {My e-mail address}
  homepage='http://h-elsner.mooo.com/';

  logminsize=10240;
  checksize=2047;
  MAVrecID=$FD;
  lenfixP=20;
  lenfix=8;
  zzf='hh:nn:ss';
  mzf='yyyy-mm-dd hh:nn';                            {Datum/Zeit Formate}
  dzf='yyyy-mm-dd';
  zzz='.zzz';
  vzf=dzf+' '+zzf;
  sep=',';
  hubsep=';';

  lipomin=3.3;                                       {Minimum LiPo voltage}
  lipomax=4.2;
  swdis=0.98;                                        {Discharge start, % from Vmax}
  vxw=999;                                           {unsinnig hoher Wert}

  msperd=86400000;                                   {ms per day}
  sperd=86400;                                       {sec per day}

implementation

{$I language.inc}
{$R *.lfm}

{ TForm1 }

procedure TForm1.FormCreate(Sender: TObject);        {Initialisierung, Sprache}
var
  fn: string;

begin
  dbg:=false;
  Caption:=rsAppName+tab2+AppVers;
  OpenDialog.Title:=capOpenDialog;
  OpenDialog.FileName:='';
  mnFile.Caption:=capFile;
  actOpen.Caption:=capOpen;
  actOpen.Hint:=hntOpen;
  mnSave.Caption:=capSave;
  actClose.Caption:=capClose;
  actClose.Hint:=hntClose;
  mnHelp.Caption:=capHelp;
  mnHomePage.Caption:=capHomepage;
  mnAbout.Caption:=capAbout;
  rgBatt.Caption:=capBatt;
  rgBatt.Hint:=hntBatt;
  cbCap.Caption:=capCap;
  cbCap.Hint:=hntCap;
  txtProtocol.Lines.Clear;
  fn:=Application.Location+rsManual;
  txtProtocol.Lines.Add(fn);
  if FileExists(fn) then
    txtProtocol.Lines.LoadFromFile(fn);
  VSerie.SeriesColor:=clNavy;
  CSerie.SeriesColor:=clFuchsia;
  Chart1.AxisList[0].Title.LabelFont.Color:=VSerie.SeriesColor;
  Chart1.AxisList[2].Title.LabelFont.Color:=CSerie.SeriesColor;
  Chart1.AxisList[0].Title.Caption:=capVolt+tab1+'[V]';
  Chart1.AxisList[2].Title.Caption:=capCap+tab1+'[%]';
  Chart1.ZoomFull;
end;

procedure TForm1.FormKeyUp(Sender: TObject; var Key: Word; Shift: TShiftState);
begin                                                {Debug version just to check thresholds}
  if ssAlt in shift then begin
    if key=88 then begin                             {Alt+X wie extra}
      dbg:=true;
      if OpenDialog.FileName<>'' then
        Zeichnen(OpenDialog.FileName);
    end;
  end;
end;

{FlightLog Formate:
 0..unbekannt
 1..Yuneec legacy (350QX, Chroma, Q500, H920, Typhoon H)
 2..Legacy H Plus, H3
 3..H920 alt
 7..Breeze
 8..TLOG (H520, Sensordateien, Mantis)

 9..Hubsan

Ermitteln, um was für ein FlightLog es sich handelt}

function vTypeToStr(const v: integer): string;       {vehicle type ausgeben}
begin
  result:='';
  case v of
    0: result:=errInvalid;
    1: result:='Yuneec H920';
    2: result:='Yuneec Q500';
    3: result:='Blade 350QX';
    4: result:='Blade Chroma (380QX)';
    5: result:='Yuneec Typhoon H';
    8: result:='PX4 TLOG (Mantis, H520, H+ Sensor';
  end;
end;

{Zeitstempel to TDateTime; Format abhängig vom Vehicle Type
 legacy Yuneec: 20151206 11:32:57:234
 Mantis Q CSV:  2019-02-28 17:53:44.401
 Breeze:        2015-12-06 11:32:57

    if btnArchive.Tag=1 then             Platform Android
      result:=result-nowUTC+now;         UTC to local time
 }

function ZeitToDT(const s: string; const vt: integer): TDateTime;
begin
  try
    case vt of
      7: result:=ScanDateTime(vzf, s);               {Breeze}
      9: result:=ScanDateTime(zzf, s);               {Time format flaretom}
    else
      result:=ScanDateTime('yyyymmdd '+zzf+':zzz', s); {Yuneec legacy format}
    end;
  except
    result:=0;
  end;
end;

{aus Yuneec Source code: LiPo Spannung in % Restkapazität}
function VtoProzY(w: TMessPkt): integer;             {vehicle_type, Spannung --> %}
const
  s61=23.9;                                          {Schwellwerte 6S}
  s62=21.7;
  s63=21.3;
  s64=21.1;

  s41=14.9;                                          {Schwellwerte 4S}
  s42=14.2;
  s43=14.0;
  s44=13.8;

  s31=10.7;                                          {Schwellwerte 3S}
  s32=10.5;
  s33=10.3;

  s21=7.2;                                           {Schwellwerte 2S   ???}
  s22=7.0;
  s23=6.8;

var
  m: double;                                         {Maximale Batteriespannung}

begin
  result:=0;                                         {default Unterspannung=0%}
  m:=w.nc*lipomax;                                   {Battery voltage}
  case w.nc of
    2: begin
         if  w.v>=m then
          result:=100;                               {100%}
         if (w.v>=s21) and
           (w.v< m)   then
          result:=round((((w.v-s21)*75)/(m-s21))+25);
         if (w.v> s22) and
           (w.v< s21) then
          result:=round((((w.v-s22)*20)/(s21-s22))+5);
         if (w.v> s23) and
           (w.v<=s22) then
          result:=round( ((w.v-s23)* 5)/(s22-s23));
       end;
    4: begin                                         {YTH / YTH Plus / H520}
         if  w.v>=m then
           result:=100;
         if (w.v>=s41) and
            (w.v< m)   then
           result:=round((((w.v-s41)*50)/(m-s41))+50);
         if (w.v> s42) and
            (w.v< s41) then
           result:=round((((w.v-s42)*25)/(s41-s42))+25);
         if (w.v> s43) and
            (w.v< s42) then
           result:=round((((w.v-s43)*20)/(s42-s43))+5);
         if (w.v> s44) and
            (w.v<=s43) then
           result:=round( ((w.v-s44)* 5)/(s43-s44));
         end;
    6: begin                                         {H920}
         if  w.v>=m then
            result:=100;
         if (w.v>=s61) and
            (w.v< m)   then
           result:=round((((w.v-s61)* 5)/(m-  s61))+95);
         if (w.v> s62) and
            (w.v< s61) then
           result:=round((((w.v-s62)*75)/(s61-s62))+20);
         if (w.v> s63) and
            (w.v< s62) then
           result:=round((((w.v-s63)* 5)/(s62-s63))+5);
         if (w.v> s64) and
            (w.v<=s63) then
           result:=round( ((w.v-s64)* 5)/(s63-s64));
       end;
  else begin                                         {alle anderen 3S Kopter}
         if  w.v>=m then
           result:=100;                              {100%}
         if (w.v>=s31) and
            (w.v< m)   then
           result:=round((((w.v-s31)*75)/(m-  s31))+25);
         if (w.v> s32) and
            (w.v< s31) then
           result:=round((((w.v-s32)*20)/(s31-s32))+5);
         if (w.v> s33) and
            (w.v<=s32) then
           result:=round( ((w.v-s33)* 5)/(s32-s33));
       end;
  end;
end;

{The relationship of voltage and capacity from RC-Groups:
 https://blog.ampow.com/lipo-voltage-chart/
 https://www.rcgroups.com/forums/showpost.php?p=29431951}

function VtoProzRC(w: TMessPkt): integer;
const
  CapTab: array [0..20] of double = (
    100,  95,   90,   85,   80,   75,   70,   65,   60,   55,   50,
    45,   40,   35,   30,   25,   20,   15,   10,   5,    0);
  S1Tab: array [0..20] of double = (
    4.20, 4.15, 4.11, 4.08, 4.02, 3.98, 3.95, 3.91, 3.87, 3.85, 3.84,
    3.82, 3.80, 3.79, 3.77, 3.75, 3.73, 3.71, 3.69, 3.61, 3.27);

var
  i: integer;                                        {index in arrays}
  uz: double;                                        {Voltage down to 1S}

begin
  result:=100;
  uz:=w.v/w.nc;                                      {Cell voltage}
  if uz<S1Tab[high(S1Tab)] then begin
    result:=0                                        {all below 3.27 = 0%}
  end else begin
    if uz<s1tab[0] then begin                        {all above 4.2V = 100%}
      for i:=0 to high(CapTab) do begin              {find next threshold}
        if uz>S1Tab[i] then
          break;                                     {Voltage inbetween delta i-1 and i}
      end;
      result:=round(CapTab[i]+((CapTab[i-1]-CapTab[i])/
                              ((S1Tab[i-1]-S1Tab[i])/(uz-S1Tab[i]))));
    end;
  end;
end;

function InFlight(const vt, fm: integer): boolean;   {Real flights}
begin
  result:=false;
  case vt of
    1, 2, 4: result:=fm in [0..14, 18, 20];          {Legacy}
    3: result:=fm in [5, 8..14, 25];                 {Blade 350 QX}
    5: result:=fm in [0..14, 18, 20..24, 26..29, 31..33];   {Typhoon H}

    6: result:=fm in [4..7, 10, 12, 13, 17];         {HPlus, H3}
    7: result:=fm in [1, 2, 16, 18];
    8: result:=fm in [2..4];                         {MAV msg}
  end;
end;

function GetS(v: integer): integer;
begin
  result:=4;                                         {Default: 4S}
  case v of
    1: result:=6;
    2..4: result:=3;
  end;
end;

{
0	MAV_TYPE_GENERIC	Generic micro air vehicle
1	MAV_TYPE_FIXED_WING	Fixed wing aircraft.
2	MAV_TYPE_QUADROTOR	Quadrotor
3	MAV_TYPE_COAXIAL	Coaxial helicopter
4	MAV_TYPE_HELICOPTER	Normal helicopter with tail rotor.
5	MAV_TYPE_ANTENNA_TRACKER	Ground installation
6	MAV_TYPE_GCS	Operator control unit / ground control station
7	MAV_TYPE_AIRSHIP	Airship, controlled
8	MAV_TYPE_FREE_BALLOON	Free balloon, uncontrolled
9	MAV_TYPE_ROCKET	Rocket
10	MAV_TYPE_GROUND_ROVER	Ground rover
11	MAV_TYPE_SURFACE_BOAT	Surface vessel, boat, ship
12	MAV_TYPE_SUBMARINE	Submarine
13	MAV_TYPE_HEXAROTOR	Hexarotor
14	MAV_TYPE_OCTOROTOR	Octorotor
15	MAV_TYPE_TRICOPTER	Tricopter
16	MAV_TYPE_FLAPPING_WING	Flapping wing
17	MAV_TYPE_KITE	Kite
18	MAV_TYPE_ONBOARD_CONTROLLER	Onboard companion controller
19	MAV_TYPE_VTOL_DUOROTOR	Two-rotor VTOL using control surfaces in vertical operation in addition. Tailsitter.
20	MAV_TYPE_VTOL_QUADROTOR	Quad-rotor VTOL using a V-shaped quad config in vertical operation. Tailsitter.
21	MAV_TYPE_VTOL_TILTROTOR	Tiltrotor VTOL
22	MAV_TYPE_VTOL_RESERVED2	VTOL reserved 2
23	MAV_TYPE_VTOL_RESERVED3	VTOL reserved 3
24	MAV_TYPE_VTOL_RESERVED4	VTOL reserved 4
25	MAV_TYPE_VTOL_RESERVED5	VTOL reserved 5
26	MAV_TYPE_GIMBAL	Gimbal
27	MAV_TYPE_ADSB	ADSB system
28	MAV_TYPE_PARAFOIL	Steerable, nonrigid airfoil
29	MAV_TYPE_DODECAROTOR	Dodecarotor
30	MAV_TYPE_CAMERA	Camera
31	MAV_TYPE_CHARGING_STATION	Charging station
32	MAV_TYPE_FLARM	FLARM collision avoidance system
33	MAV_TYPE_SERVO	Servo
34	MAV_TYPE_ODID	Open Drone ID. See https://mavlink.io/en/services/opendroneid.html.
35	MAV_TYPE_DECAROTOR	Decarotor
36	MAV_TYPE_BATTERY	Battery
}

function MAVtypeToStr(const mt: integer): string;
begin
  result:=errInvalid;
  case mt of
    0:  result:='Generic';
    1:  result:='Fixed wing';
    2:  result:='QuadRotor (Mantis Q/G)';
    13: result:='HexRotor (H520, H+, H3)';
    14: result:='OctoRotor';
    15: Result:='Tricopter';
    26: result:='Gimbal';
    30: result:='Camera';
  end;
end;

(*
{https://mavlink.io/en/messages/common.html#MAV_LANDED_STATE
 (nicht aktuell!) besser hier: https://github.com/mavlink/c_library_v2/tree/master/common
  siehe heartbeat "Verdrehung"
  0	MAV_LANDED_STATE_UNDEFINED	MAV landed state is unknown
  1	MAV_LANDED_STATE_ON_GROUND	MAV is landed (on ground)
  2	MAV_LANDED_STATE_IN_AIR	MAV is in air
  3	MAV_LANDED_STATE_TAKEOFF	MAV currently taking off
  4	MAV_LANDED_STATE_LANDING	MAV currently landing  }

function MLStoStr(const m: byte): string;            {MAV_LANDED_STATE}
begin
  case m of
    1: result:='Landed (on ground)';
    2: result:='In air';
    3: result:='Currently taking off';
    4: result:='Currently landing';
  else
    result:='MAV landed state undef';
  end;
end;     *)

function CheckFileType(logdat: TMemoryStream): integer;  {Ermitteln des Dateiformats}
var
  buf: array[0..checksize] of byte;                  {Search in the first 1 kByte}
  rawstr: string;
  i, p, len, zhl: integer;

begin
  result:=0;                                         {unbekannt}
  rawstr:='';
  try
    logdat.ReadBuffer(buf, checksize+1);
    for i:=0 to checksize do                         {Filter string from Byte stream}
      if (buf[i]>41) and (buf[i]<123) then           {Remove spaces and some unneeded chars}
        rawstr:=rawstr+chr(buf[i]);

    if pos(YLegacyID, rawstr)=1 then begin           {Überschriften suchen}
      result:=1;
      exit;
    end;
    if pos(HPlusID, rawstr)=1 then begin
      result:=2;
      exit;
    end;
    if (pos(H920ID1, rawstr)>60) and
       (Pos(H920ID2, rawstr)>60) and
       (pos(H920ID3, rawstr)>20) then begin
      result:=3;
      exit;
    end;
    if (pos(BreezeID1, rawstr)=1) and
       (pos(BreezeID2, rawstr)>10) then begin
      result:=7;
      exit;
    end;
    if pos(H501ID, rawstr)>0 then begin
      result:=9;
      exit;
    end;

    p:=0;
    zhl:=0;
    while p<(checksize-256) do begin                 {Prüfen ob MAVlink}
      len:=0;
      while (buf[p]<>MAVrecID) and
            (p<checksize) do                         {Suche Anfang Message}
        inc(p);
      len:=buf[p+1];
      if (p+len)<(checksize-len) then begin          {Mehr als eine MAVmsg im Buffer}
        p:=p+lenfixP+len;
        if buf[p]=MAVrecID then
          inc(zhl);                                  {Zähle gültige Messages}
      end;
    end;
    if zhl>6 then
      result:=8;

  except
    {ignore, result remains 0}
  end;
end;

procedure InitMP(var m: TMesspkt);                   {Default values}
begin
  m.v:=0;
  m.c:=0;
  m.vmax:=0;
  m.vmin:=vxw;
  m.nc:=3;                                           {Default 3S}
  m.segm:=1;                                         {Segment 1}
  m.pid:=0;                                          {Not charged}
  m.t:=0;
  m.td:=0;
  m.tt:=0;
  m.flt:=false;
end;

procedure TForm1.MPanalyse(var m, malt: TMesspkt);   {Kurvenanalyse Spannung}
var
  cv: double;
const
  swchrg=3.9;                                        {Batt charged, V per cell}
  swmtt=3.75;                                        {Threshold, V per cell}

begin
  cv:=m.v/m.nc;                                      {cell voltage}
  if cv>m.vmax then                                  {Find maximum voltage}
    m.vmax:=cv;
  if m.v<m.vmin then                                 {Find minimum voltage}
    m.vmin:=m.v;
  if (m.pid<>3) and
     (m.vmax>swchrg) then begin                      {Charged battery}
    m.pid:=1;
    if (m.pid=1) and
       (cv<m.vmax*swdis) then begin                  {Begin to decharge detected}
      m.pid:=2;
      if (m.pid=2) and
         (cv<swmtt) then                             {Threshold reached}
        m.pid:=3;
    end;
  end;

  if (malt.pid=1) and (m.pid=2) then
    m.td:=m.t;                                       {Start discarge}
  if (malt.pid=2) and (m.pid=3) then
    m.tt:=m.t;                                       {Met threshold}

  if m.segm<>malt.segm then begin                    {Reset values}
    m.vmax:=0;
    m.vmin:=vxw;
    m.pid:=0;
    m.td:=0;
    m.tt:=0;
    m.flt:=false;
  end;

  VSerie.AddXY(m.t, m.v);                            {Voltage}
  if dbg then
    CSerie.AddXY(m.t, m.pid)                         {Debugging: PID}
  else
    CSerie.AddXY(m.t, m.c);                          {Remaining capacity}
end;

procedure TForm1.Bewertung(mx: TMessPkt; var olist: TStringList; seg: boolean=false);
var
  w, qw1, qw2, qw3: integer;

  procedure BattCheck;
  begin
    if w>qw1 then begin
      Panel2.Color:=clGreen;
      olist.Add(rsQuali+rsBwert1);
    end else
      if w>qw2 then begin
        Panel2.Color:=clYellow;
        olist.Add(rsQuali+rsBwert2);
      end else begin
        Panel2.Color:=clRed;
        if w>qw3 then
          olist.Add(rsQuali+rsBwert3)
        else begin
          olist.Add(rsQuali+rsSchrott);
          Panel2.Caption:=rsSchrott;
        end;
      end;
    if dbg then begin
      olist.Add('Entladung bis Schwellwert: '+IntToStr(w)+'s');
      olist.Add('Schwellwerte: '+IntToStr(qw1)+' (gelb), '+
                                 IntToStr(qw2)+' (rot), '+
                                 IntToStr(qw3)+' (Schrott)')
   end;
  end;

begin
  if seg then
    olist.Add(rsSegm+' # '+IntToStr(mx.segm));       {Segmentnummer ausgeben, wenn mehr als eins}
  qw1:=400;
  qw2:=100;
  qw3:=30;
  w:=round((mx.tt-mx.td)*sperd);                     {Numerischer Wert für Güte}
  if mx.vmax>(lipomax+0.05) then begin               {High voltage LiPo}
    qw1:=600;
    qw2:=120;
    qw3:=75;
    olist.Add(rsHVLiPo);
  end;
  olist.Add(rsVmin+FormatFloat('0.0', mx.vmin)+'V');
  if lineVW2.Active then
    olist.Add(rsVW2)
  else
    if lineVW1.Active then
      olist.Add(rsVW1);
  if mx.vmin<(lipomin*mx.nc) then
    olist.Add(rsTief);
  if mx.flt then begin
    olist.Add(rsFDur+FormatDateTime('nn:ss', mx.t-mx.td)+'min');
    case mx.pid of
      0: olist.Add(rsQuali+rsNotCharged);
      1: olist.Add(rsNoStart+tab1+rsNoAnal);         {No start (discharge detected}
      2: olist.Add(rsNoData+tab1+rsNoAnal);          {Discharge detected but threshold never reached}
      3: BattCheck;                                  {Chart OK, check battery}
    end;
  end else
    olist.Add(rsNoFlight);
  olist.Add('');
end;


procedure TForm1.cbCapClick(Sender: TObject);        {Kapazität anzeigen}
begin
  CSerie.Active:=cbCap.Checked;
end;

procedure TForm1.Chart1MouseUp(Sender: TObject; Button: TMouseButton;  {Reset Zoom}
  Shift: TShiftState; X, Y: Integer);
begin
  if (ssCtrl in Shift) or                            {Klicken mit gedrückter Ctrl}
     (ssMiddle in Shift) then                        {Klicken mit mittlerer Taste}
    Chart1.ZoomFull;
end;

procedure TForm1.rgBattClick(Sender: TObject);       {Umrechnungsregel ändern}
begin
  if (OpenDialog.Filename<>'') and
      cbCap.Checked then
    Zeichnen(OpenDialog.Filename);
end;

procedure TForm1.mnAboutClick(Sender: TObject);      {About box}
begin
 MessageDlg(rsAppName+tab2+appvers+LineEnding+
            meinname+LineEnding+homepage+LineEnding+email,
            mtInformation,[mbOK],0);
end;

procedure TForm1.mnHomePageClick(Sender: TObject);   {Homepage}
begin
  OpenURL(homepage);
end;

procedure TForm1.mnSaveClick(Sender: TObject);       {Speichern}
var
  fn: string;

begin
  if OpenDialog.FileName<>'' then begin
    fn:=ChangeFileExt(OpenDialog.Filename, '')+'BT.txt';
    txtProtocol.Lines.SaveToFile(fn);
    fn:=ChangeFileExt(OpenDialog.Filename, '')+'BT.png';
    Chart1.SaveToFile(TPortableNetworkGraphic, fn);
    txtProtocol.Lines.Add(LineEnding);
    txtProtocol.Lines.Add(rsSavedTo+ChangeFileExt(fn, '.*'));
  end;
end;

procedure TForm1.actCloseExecute(Sender: TObject);   {Close application}
begin
  Close;
end;

{Breeze: Keine Spannung, keine Auswertung, nur Diagramm}

procedure TForm1.BreezeDats(logdat: TMemoryStream);  {Breeze, mode 7}
var
  inlist: TStringList;
  sar: TStringArray;
  i, fm: integer;
  mp: TMesspkt;

begin
  inlist:=TStringList.Create;
  CSerie.Active:=true;
  Vserie.Active:=false;
  cbCap.Enabled:=false;
  InitMP(mp);
  try
    inlist.LoadFromStream(logdat);
    txtProtocol.Lines.Add(rsVType+'Yuneec Breeze');
    txtProtocol.Lines.Add(rsCells+IntToStr(mp.nc)+'S');
    sar:=inlist[10].Split(sep);
    mp.t:=ZeitToDT(sar[0], 7);
    txtProtocol.Lines.Add(rsZeit+FormatDateTime(vzf, mp.t));
    for i:=10 to inlist.Count-1 do begin             {Daten auswerten}
      sar:=inlist[i].Split(sep);
      mp.t:=ZeitToDT(sar[0], 7);
      mp.v:=StrToIntDef(sar[21], 0)/2.55;
      fm:=StrToIntDef(sar[14], 1);
      CSerie.AddXY(mp.t, mp.v);                      {Capacity only}
      if InFlight(7, fm) then
        mp.flt:=true;
    end;
    lineUmin.Position:=lipomin*3;
    txtProtocol.Lines.Add(rsEZeit+FormatDateTime(vzf, mp.t));
    txtProtocol.Lines.Add('');
    if not mp.flt then
      txtProtocol.Lines.Add(rsNoFlight);
  finally
    inlist.Free;
  end;
end;

{Tom's Hubsan recorder. Hier wird nur ein Sektor untenstützt.}

procedure TForm1.H501Dats(logdat: TMemoryStream);    {Hubsan, mode 9}
var
  inlist: TStringList;
  sar: TStringArray;
  i: integer;
  mp, pmp: TMesspkt;

begin
  inlist:=TStringList.Create;
  InitMP(mp);
  InitMP(pmp);
  mp.flt:=true;                                      {immer gültiger Flug}
  mp.nc:=2;
  try
    inlist.LoadFromStream(logdat);
    txtProtocol.Lines.Add(rsVType+'Hubsan');
    txtProtocol.Lines.Add(rsCells+IntToStr(mp.nc)+'S');
    sar:=inlist[10].Split(hubsep);
    mp.t:=ZeitToDT(sar[0], 9);
    txtProtocol.Lines.Add(rsZeit+FormatDateTime(zzf, mp.t));

    for i:=10 to inlist.Count-1 do begin             {Daten auswerten}
      sar:=inlist[i].Split(hubsep);
      mp.t:=ZeitToDT(sar[0], 9);
      mp.v:=StrToFloatDef(sar[9], 0);
      case rgBatt.ItemIndex of
        0: mp.c:=VtoProzY(mp);
        1: mp.c:=VtoProzRC(mp);
      end;
      mpAnalyse(mp, pmp);
    end;
    lineUmin.Position:=lipomin*2;         {2S}
    txtProtocol.Lines.Add(rsEZeit+FormatDateTime(zzf, mp.t));
    txtProtocol.Lines.Add('');

    if mp.pid>1 then
      txtProtocol.Lines.Add(rsFDur+FormatDateTime('nn:ss', mp.t-mp.td)+'min');

(*
    inlist.Clear;
    Bewertung(mp, inlist);                           {gibt immer Schrott (0sec) aus}
    for i:=0 to inlist.Count-1 do
      txtProtocol.Lines.Add(inlist[i]);    *)
  finally
    inlist.Free;
  end;
end;

procedure TForm1.YuneecLegacy(logdat: TMemoryStream; const m: integer);
var
  inlist, outlist: TStringList;
  sar: TStringArray;
  i, vt, pfm, fm, ef: integer;
  mp, pmp: TMesspkt;

begin
  pfm:=19;                                           {default and H920 old}
  InitMP(mp);
  InitMP(pmp);
  inlist:=TStringList.Create;
  outlist:=TStringList.Create;
  try
    inlist.LoadFromStream(logdat);
    sar:=inlist[0].Split(sep);                       {Überschrift}
    for i:=10 to high(sar) do begin                  {Spalte FlightMode ermitteln}
      if sar[i]=fmodeID then begin
        pfm:=i;
        break;
      end;
    end;

    sar:=inlist[2].Split(sep);                       {Datenreihe}
    vt:=StrToIntDef(sar[pfm+2], 0);                  {Vehicle Type ermitteln}
    mp.t:=ZeitToDT(sar[0], vt);
    case m of
      2: begin
           txtProtocol.Lines.Add(rsVType+'Typhoon H+ / H3');
           mp.nc:=4;
         end;
      3: begin
           txtProtocol.Lines.Add(rsVType+rsOldFW);
           mp.nc:=6;
         end;
    else
      begin
        txtProtocol.Lines.Add(rsVType+vTypeToStr(vt));
        mp.nc:=GetS(vt);
      end;
    end;

    txtProtocol.Lines.Add(rsCells+IntToStr(mp.nc)+'S');
    txtProtocol.Lines.Add(rsZeit+FormatDateTime(vzf, mp.t));

    for i:=2 to inlist.Count-1 do begin              {Datensätze auswerten}
      sar:=inlist[i].Split(sep);
      mp.t:=ZeitToDT(sar[0], vt);
      mp.v:=0;                                       {reset voltage}
      fm:=StrToIntDef(sar[pfm], 5);                  {Flight mode, default: Angle}
      if m=2 then begin                              {H Plus, H3}
        vt:=StrToIntDef(sar[pfm+2], 0);
        if (vt=5) and (fm<20) then begin             {vehicle Type 5, keine wilden Fmodes}
          mp.v:=StrToFloatDef(sar[2], 5);
          mp.c:=StrToFloatDef(sar[3], 0);
          if InFlight(6, fm) then
            mp.flt:=true;
        end;
      end else begin                                 {Yuneec legacy}
        mp.v:=StrToFloatDef(sar[2], 5);
        ef:=StrToIntDef(sar[pfm+3], 0);              {Error flags}
        case rgBatt.ItemIndex of
          0: mp.c:=VtoProzY(mp);
          1: mp.c:=VtoProzRC(mp);
        end;
        if InFlight(vt, fm) then begin
          mp.flt:=true;
          if ((ef and 1)=1) and
             (lineVW1.Active=false) then begin       {Voltage Warning 1}
            lineVW1.Position:=mp.t;
            lineVW1.Active:=true;
          end;
          if ((ef and 2)=2) and
             (lineVW2.Active=false) then begin       {Voltage Warning 2}
            lineVW2.Position:=mp.t;
            lineVW2.Active:=true;
          end;
        end;
      end;

      if mp.v>5 then begin
        MPanalyse(mp, pmp);
        pmp:=mp;
        if (mp.pid=3) and
          (mp.v>mp.vmax*swdis*mp.nc) then begin      {Begin to decharge detected}
          mp.segm:=mp.segm+1;
        end;
      end;
    end;

    lineUmin.Position:=lipomin*mp.nc;
    txtProtocol.Lines.Add(rsEZeit+FormatDateTime(vzf, mp.t));
    txtProtocol.Lines.Add('');
    if outlist.count=0 then                          {Only one segment}
      Bewertung(mp, outlist);
    for i:=0 to outlist.Count-1 do begin             {Ergebnisse ausgeben}
      txtProtocol.Lines.Add(outlist[i]);
    end;

  finally
    inlist.Free;
    outlist.Free;
  end;
end;

{Neu bim YTH Plus/ oder Mantis Q (PX4):
 - Dateiendung *.txt
 - längster Datensatz (bisher) 156 Byte Payload
 - Fixpart 20 byte (einschließlich RecordID, aber nach MsgID mit Daten gefüllt)
 - RecordID = $FD
 - MAVlink mit MessageID 3 Bytes
 - enthält Textmessages

https://developer.yuneec.com/documentation/125/Supported-mavlink-messages
https://github.com/mavlink/c_library_v2/tree/master/common

 Dieses Format wird auch beim MantisQ als FlightLog geschrieben bzw. als
 tlog Datei beim H520 oder als Sensordatei vom H3/H Plus}

procedure TForm1.MAVmsg(const logdat: TMemoryStream);  {TLOG, Sensor, Mantis}
var
  dsbuf: array[0..280] of byte;
  i, e, mavtype: integer;
  len: uint8;
  b: byte;
  bg, begt: TDateTime;                               {System time}
  begts: TDateTime;                                  {Boot time}
  lts, toffs: Int64;
  mp, pmp: TMesspkt;
  outlist: TStringList;

  function GetIntFromBuf(const p, a: integer): uint64; {Position/Anzahl Bytes}
  var
    i: integer;

  begin
    result:=0;
    for i:=0 to a-1 do begin
      result:=result+dsbuf[lenfix+i+p]*(256**i);
    end;
  end;

  procedure DataPoint;
  begin
    MPanalyse(mp, pmp);
    if mp.segm<>pmp.segm then                        {New segment}
      Bewertung(pmp, outlist, true);
    pmp:=mp;                                         {set previous dataset}
  end;

  procedure Heartbeat;                               {MAV_State aus Heartbeat}
  begin
    if dsbuf[lenfix-4]=1 then begin                  {Ausgaben nur für AUTOPILOT1}
      mavtype:=dsbuf[lenfix+4];                      {Type, Quad ---> Mantis}
    end;
  end;

  procedure MACsysStatus;                            {MAV_SYS_STATUS 1}
  begin
    mp.v:=GetIntFromBuf(14, 2)/1000;                 {Battery voltage}
    mp.c:=dsbuf[lenfix+30];                          {Remaining battery capacity}
    DataPoint;
  end;

  procedure BattStatus;                              {BATTERY_STATUS 147 ($93)}
  var
    i, w, volts, nz: integer;

  begin
    volts:=0;
    nz:=0;
    for i:=0 to 9 do begin                           {Voltage for max 10 cells}
      w:=GetIntFromBuf(i*2+10, 2);
      if w<60000 then begin
        volts:=volts+w;                              {Zellen aufsummieren}
        inc(nz);                                     {Zellen zählen}
      end;
    end;
    mp.v:=volts/1000;                                {Battery voltage}
    mp.nc:=nz;                                       {Number cells}

    w:=GetIntFromBuf(35, 1);                         {Remaining capacity}
    if w>=0 then
      mp.c:=w;                                       {remaining capacity [%]}
    DataPoint;
  end;

  procedure Timestamp;                               {Zeitverlauf berechnen}
  var t: Int64;

  begin
    t:=GetIntFromBuf(0, 4);                          {in ms}
    if (t+toffs)<(lts-60000) then begin              {Time reset, delta 1 min}
      toffs:=lts;
      mp.segm:=mp.segm+1;                            {Next segment}
    end;
    mp.t:=(t+toffs)/msperd;                          {Add time to this segment}
    if (begts=0) and (lts>0) then begin
      begts:=mp.t;
    end;
    lts:=t+toffs;                                    {Save as previous time stamp}
  end;

begin
  rgBatt.Enabled:=false;
  InitMP(mp);
  InitMP(pmp);
  outlist:=TStringList.Create;
  mp.nc:=4;                                          {Default: 4S Batt}
  mavtype:=0;

  bg:=0;                                             {System time}
  begt:=0;
  begts:=0;
  toffs:=0;
  lts:=0;
  try
    while (logdat.Position<(logdat.Size-lenfix)) do begin  {bis zum Ende der Datei}
      len:=0;                                        {Reset for error detection}
      try
        repeat
          b:=logdat.ReadByte;
        until (b=MAVrecID) or (logdat.Position>(logdat.Size-lenfix));
        len:=logdat.ReadByte;                        {Länge Payload mit CRC}
        logdat.ReadBuffer(dsbuf, len+lenfixP-2);     {Lese Rest-Datensatz in den Buffer}

        e:=GetIntFromBuf(-3, 3);                     {Message ID}
        case e of
          0: Heartbeat;                              {MavType}
          2: bg:=UnixToDateTime(GetIntFromBuf(0, 8) div 1000000); {SystemTime UNIX [us]}
          1: MACsysStatus;                           {Volt, Batt remain}
          147: BattStatus;
          245: if InFlight(8, dsbuf[lenfix+1]) then  {MAV_landed_state 1-ground, 2..4-air}
                 mp.flt:=true;
          30, 32, 33, 65: Timestamp;                 {ms}
        end;

        if (begt=0) and (bg>0) then                  {Begin system time setzen}
          begt:=bg;

      except
        on e: Exception do begin
          break;
        end;
      end;
    end;
    lineUmin.Position:=lipomin*mp.nc;
    txtProtocol.Lines.Add('');
    txtProtocol.Lines.Add(rsVType+MAVtypeToStr(mavtype));
    txtProtocol.Lines.Add(rsCells+IntToStr(mp.nc)+'S');
    if (begt>0) and (bg>begt) then begin             {Systemzeit vorhanden}
      txtProtocol.Lines.Add(rsZeit+FormatDateTime(vzf, begt));
      txtProtocol.Lines.Add(rsEZeit+FormatDateTime(vzf, bg));
    end else begin                                   {Sensordatei, keine Systemzeit}
      txtProtocol.Lines.Add(rsZeit+FormatDateTime(zzf, begts));
      txtProtocol.Lines.Add(rsEZeit+FormatDateTime(zzf, mp.t));
    end;
    txtProtocol.Lines.Add('');

    if outlist.count=0 then                          {Only one segment}
      Bewertung(mp, outlist);
    for i:=0 to outlist.Count-1 do
      txtProtocol.Lines.Add(outlist[i]);
  finally
    outlist.Free;
  end;
end;

procedure TForm1.Zeichnen(const fn: string);         {Ein FlightLog auswerten}
var
  vtf: integer;                                      {Vehicle type from file}
  logf: TMemoryStream;
  ddl: char;

begin
  Chart1.ZoomFull(true);
  rgBatt.Enabled:=true;
  cbCap.Enabled:=true;
  Caption:=rsAppName+tab2+ExtractFileName(fn);
  txtProtocol.Lines.Clear;
  txtProtocol.Lines.Add(fn);
  txtProtocol.Lines.Add('');
  CSerie.Active:=cbCap.Checked;
  Panel2.Color:=Panel1.Color;
  Panel2.Caption:='';

  if FileSize(fn)>logminsize then begin
    logf:=TMemoryStream.Create;
    Screen.Cursor:=crHourGlass;
    ddl:=DefaultFormatSettings.DecimalSeparator;     {Dezimaltrenner speichern}
    DefaultFormatSettings.DecimalSeparator:='.';     {Yuneec Format}
    VSerie.Clear;
    CSerie.Clear;
    lineUmin.Active:=false;
    lineVW1.Active:=false;
    lineVW2.Active:=false;

    try
      logf.LoadFromFile(fn);
      vtf:=CheckFileType(logf);                      {Vehicle type from file}
      logf.Position:=0;
      case vtf of
        0: txtProtocol.Lines.Add(errUnknown+tab1+rsNoAnal);
        1..3: YuneecLegacy(logf, vtf);
        7: BreezeDats(logf);
        8: MAVmsg(logf);
        9: H501Dats(logf);
      end;
      if vtf>0 then
        lineUmin.Active:=true;

    finally
      DefaultFormatSettings.DecimalSeparator:=ddl;   {Original wiederherstellen}
      logf.Free;
      Screen.Cursor:=crDefault;
      Chart1.ZoomFull(true);
    end;

  end else
    txtProtocol.Lines.Add(rsFileSize+tab1+rsNoData); {Datei zu klein zum Spielen}
end;

procedure TForm1.actOpenExecute(Sender: TObject);    {Ein FlightLog öffnen}
begin
  rgBatt.Enabled:=true;
  cbCap.Enabled:=true;
  Panel2.Color:=Panel1.Color;
  Panel2.Caption:='';
  if OpenDialog.Execute then begin
   dbg:=false;
   Zeichnen(OpenDialog.FileName);
  end else
    Caption:=rsAppName+tab2+AppVers;
end;

end.

