//*****************************************************************************
//                 INCLUDES -- Start
//*****************************************************************************
#include <stdio.h>
#include <string.h>

// Simplelink includes
#include "simplelink.h"

//Driverlib includes
#include "hw_types.h"
#include "hw_ints.h"
#include "rom.h"
#include "rom_map.h"
#include "interrupt.h"
#include "prcm.h"
#include "utils.h"
#include "uart.h"
#include "hw_memmap.h"
#include "hw_common_reg.h"
#include "hw_apps_rcm.h"
#include "gpio.h"
#include "timer.h"
#include "Adafruit_GFX.h"
#include "spi.h"

//Common interface includes
#include "pinmux.h"
#include "Adafruit_SSD1351.h"
#include "timer_if.h"
#include "gpio_if.h"
#include "common.h"
#include "uart_if.h"
//*****************************************************************************
//                 INCLUDES -- End
//*****************************************************************************

//*****************************************************************************
//                 DEFINES -- Start
//*****************************************************************************
#define MAX_URI_SIZE 128
#define URI_SIZE MAX_URI_SIZE + 1

//SPI data
#define SPI_IF_BIT_RATE  100000
#define TR_BUFF_SIZE     100

//Screen data
#define SCREEN_HEIGHT 128
#define SCREEN_WIDTH 128
#define SQUARE_SIZE 41
#define LINE_COLOR 0x07FF
#define X_COLOR 0xF800
#define O_COLOR 0x07E0
#define NUMBER_COLOR 0xF81F
#define BG_COLOR 0x0
#define CHAR_SIZE 3

//Tic-tac-toe data
#define PLAYER_X 'X'
#define PLAYER_O 'O'
#define EMPTY_SPACE ' '
#define NO_WIN 0
#define WIN 1
#define DRAW 2

//Times are in ms
#define SIGNAL_LENGTH_MS 26
#define GET_REQUEST_CHECK_MS 5000

//Time is in ticks
#define DOUBLE_SEND_THRESHHOLD_TK 64000000
#define GET_REQUEST_CHECK_TK 400000000

//Key defines
#define UNKNOWN 63 //maps to ?
#define NO_KEY 46 //maps to .

//Simplelink data
#define APPLICATION_NAME        "SSL"
#define APPLICATION_VERSION     "1.1.1.EEC.Spring2018"
#define SERVER_NAME             "a24stzee4oei9t.iot.us-east-1.amazonaws.com"
#define GOOGLE_DST_PORT         8443

//Certificate paths
#define SL_SSL_CA_CERT "/cert/rootCA"
#define SL_SSL_PRIVATE "/cert/private"
#define SL_SSL_CLIENT  "/cert/client"

//NEED TO UPDATE THIS FOR IT TO WORK!
#define DATE                5    /* Current Date */
#define MONTH               6     /* Month 1-12 */
#define YEAR                2018  /* Current year */
#define HOUR                0    /* Time - hours */
#define MINUTE              37    /* Time - minutes */
#define SECOND              0     /* Time - seconds */

//RESTful API
#define POSTHEADER "POST /things/CC3200Thing/shadow HTTP/1.1\n\r"
#define GETHEADER "GET /things/CC3200Thing/shadow HTTP/1.1\n\r"
#define HOSTHEADER "Host: a24stzee4oei9t.iot.us-east-1.amazonaws.com\r\n"
#define CHEADER "Connection: Keep-Alive\r\n"
#define CTHEADER "Content-Type: application/json; charset=utf-8\r\n"
#define CLHEADER1 "Content-Length: "
#define CLHEADER2 "\r\n\r\n"
#define DATA_TEST "{\"state\": {\r\n\"desired\" : {\r\n\"var\" : \"Anyone out there?\"\r\n}}}\r\n\r\n"
//*****************************************************************************
//                 DEFINES -- End
//*****************************************************************************

//*****************************************************************************
//                 DATA STRUCTURES -- Start
//*****************************************************************************
// Application specific status/error codes
typedef enum{
    // Choosing -0x7D0 to avoid overlap w/ host-driver's error codes
    LAN_CONNECTION_FAILED = -0x7D0,
    INTERNET_CONNECTION_FAILED = LAN_CONNECTION_FAILED - 1,
    DEVICE_NOT_IN_STATION_MODE = INTERNET_CONNECTION_FAILED - 1,

    STATUS_CODE_MAX = -0xBB8
}e_AppStatusCodes;

typedef struct
{
   /* time */
   unsigned long tm_sec;
   unsigned long tm_min;
   unsigned long tm_hour;
   /* date */
   unsigned long tm_day;
   unsigned long tm_mon;
   unsigned long tm_year;
   unsigned long tm_week_day; //not required
   unsigned long tm_year_day; //not required
   unsigned long reserved[3];
}SlDateTime;
//*****************************************************************************
//                 DATA STRUCTURES -- End
//*****************************************************************************

//*****************************************************************************
//                 GLOBAL VARIABLES -- Start
//*****************************************************************************
volatile unsigned long  g_ulStatus = 0;//SimpleLink Status
unsigned long  g_ulPingPacketsRecv = 0; //Number of Ping Packets received
unsigned long  g_ulGatewayIP = 0; //Network Gateway IP address
unsigned char  g_ucConnectionSSID[SSID_LEN_MAX+1]; //Connection SSID
unsigned char  g_ucConnectionBSSID[BSSID_LEN_MAX]; //Connection BSSID
signed char    *g_Host = SERVER_NAME;
SlDateTime g_time;
#if defined(ccs) || defined(gcc)
extern void (* const g_pfnVectors[])(void);
#endif
#if defined(ewarm)
extern uVectorEntry __vector_table;
#endif

extern void (* const g_pfnVectors[])(void);
static volatile unsigned long edge_count;
static volatile unsigned long signal_base;
static volatile unsigned long get_base;
static volatile unsigned int timer_recordings[128];
//static volatile unsigned char must_be_new_letter;
//static volatile unsigned char previous_key;
//static volatile unsigned char num_repeats;
//static volatile int char_position;
//static volatile int drawNow;
//static char sender_message[200];
//static char receiver_message[200];
static volatile char current_player;
static volatile char current_board[9];
static volatile char winning_player;
static volatile int selected_space;
static char DATA1[300];
static char DATA2[300];
long mainLRetVal;

//*****************************************************************************
//                 GLOBAL VARIABLES -- End
//*****************************************************************************

//****************************************************************************
//                      LOCAL FUNCTION PROTOTYPES - Start
//****************************************************************************
static long WlanConnect();
static int set_time();
static long InitializeAppVariables();
static int tls_connect();
static int connectToAccessPoint();
static int http_post(int);
static int http_get(int);

static void BoardInit(void);
static void SPIInit(void);
static void OLEDInit(void);
static void GPIOInit(void);
static void TimersInit(void);
static void TicTacToeInit(void);
static void DrawX(unsigned int pos);
static void DrawO(unsigned int pos);
static void DrawNumber(unsigned int pos);
static void SelectSpace(unsigned int pos);
static void DeselectSpace(unsigned int pos);
static void ClearSpace(unsigned int pos);
static void RisingEdgeHandler(void);
static void FallingEdgeHandler(void);
static void StartTimerHandler(void);
static void OnTimerEndHandler(void);
static void OnGetEndHandler(void);
static void SW2Handler(void);
static void SW3Handler(void);
//static void UARTReceiveHandler(void);
static unsigned char DetermineNumber(int input);
static void SendToAWS(int result);
static void GetBoardString(char *buf);
static void ConnectToAWS(void);
static int CheckForWin(void);
static void EndGame(int result);
static void DrawEndGame(int result);
//****************************************************************************
//                      LOCAL FUNCTION PROTOTYPES - End
//****************************************************************************

//*****************************************************************************
//                 PIN SETUP -- Start
//*****************************************************************************
typedef struct PinSetting {
    unsigned long port;
    unsigned int pin;
} PinSetting;

static PinSetting receiver_rising = { .port = GPIOA0_BASE, .pin = 0x1};
static PinSetting receiver_falling = { .port = GPIOA3_BASE, .pin = 0x40};
static PinSetting sw2 = { .port = GPIOA2_BASE, .pin = 0x40};
static PinSetting sw3 = { .port = GPIOA1_BASE, .pin = 0x20};
//*****************************************************************************
//                 PIN SETUP -- End
//*****************************************************************************

//*****************************************************************************
//                 INITIALIZERS -- Start
//*****************************************************************************
static void BoardInit(void) {
/* In case of TI-RTOS vector table is initialize by OS itself */
#ifndef USE_TIRTOS
  //
  // Set vector table base
  //
#if defined(ccs)
    MAP_IntVTableBaseSet((unsigned long)&g_pfnVectors[0]);
#endif
#if defined(ewarm)
    MAP_IntVTableBaseSet((unsigned long)&__vector_table);
#endif
#endif
    //
    // Enable Processor
    //
    MAP_IntMasterEnable();
    MAP_IntEnable(FAULT_SYSTICK);

    PRCMCC3200MCUInit();
}

//Initilializes SPI
static void SPIInit(void)
{
    // Enable the SPI module clock
    MAP_PRCMPeripheralClkEnable(PRCM_GSPI,PRCM_RUN_MODE_CLK);

    // Reset the peripheral
    MAP_PRCMPeripheralReset(PRCM_GSPI);

    //Reset SPI
    MAP_SPIReset(GSPI_BASE);

    //Configure SPI
    MAP_SPIConfigSetExpClk(GSPI_BASE,MAP_PRCMPeripheralClockGet(PRCM_GSPI),
                        SPI_IF_BIT_RATE,SPI_MODE_MASTER,SPI_SUB_MODE_0,
                        (SPI_SW_CTRL_CS |
                        SPI_4PIN_MODE |
                        SPI_TURBO_OFF |
                        SPI_CS_ACTIVEHIGH |
                        SPI_WL_8));

    //Enable SPI for communication
    MAP_SPIEnable(GSPI_BASE);
}

static void OLEDInit(void)
{
    //Initializes the OLED screen to a tic-tac-toe board with numbers
    Adafruit_Init();
    fillScreen(BG_COLOR);
    drawLine(0, 41, 127, 41, LINE_COLOR);
    drawLine(0, 83, 127, 83, LINE_COLOR);
    drawLine(41, 0, 41, 127, LINE_COLOR);
    drawLine(83, 0, 83, 127, LINE_COLOR);

//    int i;
//    for(i = 1; i <= 9; ++i)
//    {
//        DrawNumber(i);
//    }

    SelectSpace(1);
}

static void GPIOInit(void)
{
    // Register the interrupt handlers
    MAP_GPIOIntRegister(receiver_rising.port, RisingEdgeHandler);
    MAP_GPIOIntRegister(receiver_falling.port, StartTimerHandler); //Initially set to start timer on trigger
    MAP_GPIOIntRegister(sw2.port, SW2Handler);
    MAP_GPIOIntRegister(sw3.port, SW3Handler);

    // Configure edge interrupts
    MAP_GPIOIntTypeSet(receiver_rising.port, receiver_rising.pin, GPIO_RISING_EDGE);
    MAP_GPIOIntTypeSet(receiver_falling.port, receiver_falling.pin, GPIO_FALLING_EDGE);
    MAP_GPIOIntTypeSet(sw2.port, sw2.pin, GPIO_RISING_EDGE);
    MAP_GPIOIntTypeSet(sw3.port, sw3.pin, GPIO_RISING_EDGE);

    //Clear interrupts
    MAP_GPIOIntClear(receiver_rising.port, receiver_rising.pin);
    MAP_GPIOIntClear(receiver_falling.port, receiver_falling.pin);
    MAP_GPIOIntClear(sw2.port, sw2.pin);
    MAP_GPIOIntClear(sw3.port, sw3.pin);

    //Enable falling edge interrupt only
    MAP_GPIOIntEnable(receiver_falling.port, receiver_falling.pin);

    //Enable both switches
    MAP_GPIOIntEnable(sw2.port, sw2.pin);
    MAP_GPIOIntEnable(sw3.port, sw3.pin);
}

//Function to initialize the Timers
static void TimersInit(void)
{
    signal_base = TIMERA0_BASE;
    get_base = TIMERA1_BASE;
    Timer_IF_Init(PRCM_TIMERA0, signal_base, TIMER_CFG_ONE_SHOT, TIMER_A, 0);
    Timer_IF_Init(PRCM_TIMERA1, get_base, TIMER_CFG_ONE_SHOT, TIMER_A, 0);
    Timer_IF_IntSetup(signal_base, TIMER_A, OnTimerEndHandler);
    Timer_IF_IntSetup(get_base, TIMER_A, OnGetEndHandler);
    Timer_IF_InterruptClear(signal_base);
    Timer_IF_InterruptClear(get_base);
}

//Function to initialize UART
/*
static void UARTInit(void)
{
    MAP_UARTConfigSetExpClk(UARTA1_BASE,
                            MAP_PRCMPeripheralClockGet(PRCM_UARTA1),
                            UART_BAUD_RATE,
                            (UART_CONFIG_WLEN_8 | UART_CONFIG_STOP_ONE | UART_CONFIG_PAR_NONE)
                            );

    //Set up interrupts
    UARTFIFOLevelSet(UARTA1_BASE, UART_FIFO_TX1_8, UART_FIFO_RX1_8);
    UARTIntRegister(UARTA1_BASE, UARTReceiveHandler);
    UARTIntClear(UARTA1_BASE, UART_INT_RX|UART_INT_RT);
    UARTIntEnable(UARTA1_BASE, UART_INT_RX|UART_INT_RT);

    //Enable communication
    UARTEnable(UARTA1_BASE);
}
*/

//Set up an empty ttt board and set X to go first
static void TicTacToeInit(void)
{
    current_player = PLAYER_X;
    winning_player = EMPTY_SPACE;
    selected_space = 1;
    int i;
    for(i = 0; i < 9; ++i)
    {
        current_board[i] = EMPTY_SPACE;
    }
}

static void ConnectToAWS(void)
{
    long lRetVal = -1;

    //Connect the CC3200 to the local access point
    lRetVal = connectToAccessPoint();
    //Set time so that encryption can be used
    lRetVal = set_time();
    if(lRetVal < 0) {
        UART_PRINT("Unable to set time in the device");
        LOOP_FOREVER();
    }
    //Connect to the website with TLS encryption
    lRetVal = tls_connect();
    if(lRetVal < 0) {
        ERR_PRINT(lRetVal);
    }

    mainLRetVal = lRetVal;
}
//*****************************************************************************
//                 INITIALIZERS -- End
//*****************************************************************************

//*****************************************************************************
//                 HANDLERS -- Start
//*****************************************************************************
static void SW2Handler(void)
{
    MAP_GPIOIntClear(sw2.port, sw2.pin);
    UART_PRINT("SW2!\n\r");
    DeselectSpace(selected_space);
    ++selected_space;
    if(selected_space == 10)
        selected_space = 1;
    SelectSpace(selected_space);
}

static void SW3Handler(void)
{
    MAP_GPIOIntClear(sw3.port, sw3.pin);
    UART_PRINT("SW3!\n\r");

    if(current_board[selected_space - 1] == EMPTY_SPACE) //is valid move
    {
        if(current_player == PLAYER_X)
        {
            DrawX(selected_space);
            current_board[selected_space - 1] = PLAYER_X;
            int result = CheckForWin();
            if(result != NO_WIN)
            {
                EndGame(result);
            }
            current_player = PLAYER_O;
        }
        else
        {
            DrawO(selected_space);
            current_board[selected_space - 1] = PLAYER_O;
            int result = CheckForWin();
            if(result != NO_WIN)
            {
                EndGame(result);
            }
            current_player = PLAYER_X;
        }
        //SendToAWS();
    } //valid move
}

//This handler gets triggered when we have a rising edge, and records the current timer for the
//the message we received from the IR remote, then increases the edge count we got
static void RisingEdgeHandler(void)
{
    //Clear interrupts
    MAP_GPIOIntClear(receiver_rising.port, receiver_rising.pin);

    //Record timer value
    timer_recordings[edge_count] = Timer_IF_GetCount(signal_base, TIMER_A);
    edge_count++;
}

//This handler gets triggered when we have a rising edge, and records the current timer for the
//the message we received from the IR remote, then increases the edge count we got
static void FallingEdgeHandler(void)
{
    //Clear interrupts
    MAP_GPIOIntClear(receiver_falling.port, receiver_falling.pin);

    //Record timer value
    timer_recordings[edge_count] = Timer_IF_GetCount(signal_base, TIMER_A);
    edge_count++;
}

//Called once the first falling edge is triggered, indicating a signal start
static void StartTimerHandler(void)
{
    //Clear signal timer interrupt
    Timer_IF_InterruptClear(signal_base);

    //Clear pin interrupt
    MAP_GPIOIntClear(receiver_falling.port, receiver_falling.pin);

    //Reset edge count
    edge_count = 0;

    //Enable rising edge interrupt handler, re-map falling edge handler, and start timer
    MAP_GPIOIntEnable(receiver_rising.port, receiver_rising.pin);
    MAP_GPIOIntRegister(receiver_falling.port, FallingEdgeHandler);
    Timer_IF_Start(signal_base, TIMER_A, SIGNAL_LENGTH_MS);
}

//Called after the signal timer has timed out, meaning we've (hopefully) read a valid signal
static void OnTimerEndHandler(void)
{
    // Clear the signal timer interrupt and stop it
    Timer_IF_InterruptClear(signal_base);
    Timer_IF_Stop(signal_base, TIMER_A);

    //Disable handlers while we parse input
    MAP_GPIOIntDisable(receiver_falling.port, receiver_falling.pin);
    MAP_GPIOIntDisable(receiver_rising.port, receiver_rising.pin);

    //Parse input
    if(edge_count > 20) //check if valid signal, if not ignore
    {
        //Set up variables
        int current = 1; //signal starts by sending a 1
        int previous;
        int result = 0; //MUST be set to 0 since we'll do bit operations on it

        //Extract 1s and 0s
        int i = edge_count - 8;
        previous = timer_recordings[i];
        for(; i < edge_count; ++i)
        {
            //gets the time for each bit we received from the IR remote
            //and stores each bit value we receive
            timer_recordings[i] -= previous;
            previous += timer_recordings[i];
            //if there was a large delay, change the current bit to the opposite bit
            if(timer_recordings[i] > 100000){
                if(current == 0)
                {
                    current = 1;
                }
                else
                {
                    current = 0;
                }
            }
            //gets the result and makes it into a bit key for each signal
            result = (result << 1) | current;
        }

        //Convert to key and perform appropriate action
        unsigned char now = DetermineNumber(result); //this function takes the result we got above
        if(now == UNKNOWN)
        {
            //do nothing
        }
        /*
        else if(now == LAST)
        {
            //if last, then insert a NO_KEY into a string, and send the message
            //This should also clear the sender's message on the OLED
             sender_message[char_position] = NO_KEY;
             sender_message[char_position+1] = '\0';
             //ClearSender();
             SendOverUART();
        }
        */
        else //numeric key
        {
            int pos = now - '0'; //convert to integer
            if(current_board[pos - 1] == EMPTY_SPACE) //is valid move
            {
                if(current_player == PLAYER_X)
                {
                    DrawX(pos);
                    current_board[pos - 1] = PLAYER_X;
                    current_player = PLAYER_O;
                }
                else
                {
                    DrawO(pos);
                    current_board[pos - 1] = PLAYER_O;
                    current_player = PLAYER_X;
                }
                //SendToAWS();
            } //valid move
        } //numeric key

        //reset some variables
//        previous_key = now;
//        must_be_new_letter = 0;
    } //valid signal

    //Re-enable falling edge and re-map to trigger on next timer start
    MAP_GPIOIntRegister(receiver_falling.port, StartTimerHandler);
    MAP_GPIOIntEnable(receiver_falling.port, receiver_falling.pin);
}

//Update the board state by reading from AWS
static void OnGetEndHandler(void)
{
    //Clear wait timer interrupt
    Timer_IF_InterruptClear(get_base);

    UART_PRINT("In OnGetEndHandler\n\r");

    //Get data from AWS
    http_get(mainLRetVal);

    //Restart timer
    Timer_IF_Start(get_base, TIMER_A, GET_REQUEST_CHECK_MS);
}

/*
//called when receiving a message
static void UARTReceiveHandler(void)
{
    //Clear interrupt
    UARTIntClear(UARTA1_BASE, UART_INT_RX|UART_INT_RT);

    //Parse message
    int pos;
    long received;
    //while there is something in the SPI queue, get the next character until empty
    while(UARTCharsAvail(UARTA1_BASE)){
      pos = strlen(receiver_message);
      //function to get character from queue
      received = UARTCharGetNonBlocking(UARTA1_BASE);
      if(received == NO_KEY) //end of transmission
      {
          drawNow = 1; //set drawNow flag that will print the message out in Main
      }
      else //save transmission
      {
          //save message in receive character Array
          receiver_message[pos] = received;
          receiver_message[pos+1] = '\0';
      }
    }
}
*/
//*****************************************************************************
//                 HANDLERS -- End
//*****************************************************************************

//*****************************************************************************
//                 UART -- Start
//*****************************************************************************
static void SendToAWS(int result)
{
    //Pause GET timer
//    MAP_TimerDisable(get_base,TIMER_A);

//    char buf[12]; //9 spots for board, 1 for win, 1 for cur, 1 for \0
//    GetBoardString(&buf[0]);
//    strcat(DATA1, "{\"state\": {\r\n\"desired\" : {\r\n\"var\": \"");
//    strcat(DATA1, buf);
//    strcat(DATA1, "\"\r\n}}}\r\n\r\n");

    DATA1[0] = '\0';
    strcat(DATA1, "{\"state\": {\r\n\"desired\" : {\r\n\"default\": \"Congrats to player ");
    if(result == WIN && current_player == PLAYER_X)
        strcat(DATA1, "X");
    else if(result == WIN && current_player == PLAYER_O)
        strcat(DATA1, "O");
    else
        strcat(DATA1, "NOBODY");
    strcat(DATA1, "!!\"\r\n}}}\r\n\r\n");
    printf(DATA1);

    //for the length of Sender_message, put each character in the array into the SPI Queue
    //for the receiver to get later
    http_post(mainLRetVal);
    //Reset sender
    DATA1[0] = '\0';

    //Resume GET timer
//    MAP_TimerEnable(get_base,TIMER_A);
}
//*****************************************************************************
//                 UART -- End
//*****************************************************************************

//*****************************************************************************
//                 DRAWING -- Start
//*****************************************************************************

//Each space is 41px by 41px
static void DrawX(unsigned int pos)
{
    int x = ((pos - 1) % 3) * (SQUARE_SIZE + 1) + 7;
    int y = ((pos - 1) / 3) * (SQUARE_SIZE + 1) + 7;
    drawChar(x, y, PLAYER_X, X_COLOR, BG_COLOR, CHAR_SIZE);
}

static void DrawO(unsigned int pos)
{
    int x = ((pos - 1) % 3) * (SQUARE_SIZE + 1) + 7;
    int y = ((pos - 1) / 3) * (SQUARE_SIZE + 1) + 7;
    drawChar(x, y, PLAYER_O, O_COLOR, BG_COLOR, CHAR_SIZE);
}

static void DrawNumber(unsigned int pos)
{
    int x = ((pos - 1) % 3) * (SQUARE_SIZE + 1) + 7;
    int y = ((pos - 1) / 3) * (SQUARE_SIZE + 1) + 7;
    drawChar(x, y, '0'+pos, NUMBER_COLOR, BG_COLOR, CHAR_SIZE);
}

static void SelectSpace(unsigned int pos)
{
    int x = ((pos - 1) % 3) * (SQUARE_SIZE + 1) + 3;
    int y = ((pos - 1) / 3) * (SQUARE_SIZE + 1) + 3;
    drawRect(x, y, SQUARE_SIZE - 6, SQUARE_SIZE - 6, NUMBER_COLOR);
}

static void DeselectSpace(unsigned int pos)
{
    int x = ((pos - 1) % 3) * (SQUARE_SIZE + 1) + 3;
    int y = ((pos - 1) / 3) * (SQUARE_SIZE + 1) + 3;
    drawRect(x, y, SQUARE_SIZE - 6, SQUARE_SIZE - 6, BG_COLOR);
}

static void ClearSpace(unsigned int pos)
{
    int x = ((pos - 1) % 3) * (SQUARE_SIZE + 1) + 1;
    int y = ((pos - 1) / 3) * (SQUARE_SIZE + 1) + 1;
    fillRect(x, y, SQUARE_SIZE - 1, SQUARE_SIZE - 1, BG_COLOR);
}

static void DrawEndGame(int result)
{
    if(result == WIN)
    {
        fillScreen(BG_COLOR);
        if(current_player == PLAYER_X)
            drawChar(10, 10, PLAYER_X, X_COLOR, BG_COLOR, CHAR_SIZE*2);
        else
            drawChar(10, 10, PLAYER_O, O_COLOR, BG_COLOR, CHAR_SIZE*2);
        drawChar(40, 70, 'W', NUMBER_COLOR, BG_COLOR, CHAR_SIZE);
        drawChar(60, 70, 'I', NUMBER_COLOR, BG_COLOR, CHAR_SIZE);
        drawChar(80, 70, 'N', NUMBER_COLOR, BG_COLOR, CHAR_SIZE);
        drawChar(100, 70, 'S', NUMBER_COLOR, BG_COLOR, CHAR_SIZE);
    }
    else
    {
        drawChar(40, 70, 'D', NUMBER_COLOR, BG_COLOR, CHAR_SIZE);
        drawChar(60, 70, 'R', NUMBER_COLOR, BG_COLOR, CHAR_SIZE);
        drawChar(80, 70, 'A', NUMBER_COLOR, BG_COLOR, CHAR_SIZE);
        drawChar(100, 70, 'W', NUMBER_COLOR, BG_COLOR, CHAR_SIZE);
    }
}
//*****************************************************************************
//                 DRAWING -- End
//*****************************************************************************

//*****************************************************************************
//                 OTHER METHODS -- Start
//*****************************************************************************
//Convert signal to key number, by determing what the result variable corresponds to
static unsigned char DetermineNumber(int input)
{
    switch(input)
    {
    case 255: //0
        return UNKNOWN;
    case 252: //1
        return '1';
    case 253: //2
        return '2';
    case 240: //3
        return '3';
    case 247: //4
        return '4';
    case 244: //5
        return '5';
    case 241: //6
        return '6';
    case 192: //7
        return '7';
    case 223: //8
        return '8';
    case 220: //9
        return '9';
    }

    return UNKNOWN;
}

static void GetBoardString(char *buf)
{
    int i;
    for(i = 0; i < 9; ++i)
    {
        buf[i] = current_board[i];
    }
    buf[9] = winning_player;
    buf[10] = current_player;
    buf[11] = '\0';
}

static int CheckForWin(void)
{
    //First check for win
    if(
            ((current_board[0] != EMPTY_SPACE) && (current_board[0] == current_board[1]) && (current_board[1] == current_board[2])) ||
            ((current_board[3] != EMPTY_SPACE) && (current_board[3] == current_board[4]) && (current_board[4] == current_board[5])) ||
            ((current_board[6] != EMPTY_SPACE) && (current_board[6] == current_board[7]) && (current_board[7] == current_board[8])) ||
            ((current_board[0] != EMPTY_SPACE) && (current_board[0] == current_board[3]) && (current_board[3] == current_board[6])) ||
            ((current_board[1] != EMPTY_SPACE) && (current_board[1] == current_board[4]) && (current_board[4] == current_board[7])) ||
            ((current_board[2] != EMPTY_SPACE) && (current_board[2] == current_board[5]) && (current_board[5] == current_board[8])) ||
            ((current_board[0] != EMPTY_SPACE) && (current_board[0] == current_board[4]) && (current_board[4] == current_board[8])) ||
            ((current_board[2] != EMPTY_SPACE) && (current_board[2] == current_board[4]) && (current_board[4] == current_board[6]))
      )
        return WIN;

    //Then check for draw
    int i;
    for(i = 0; i < 9; ++i)
    {
        if(current_board[i] == EMPTY_SPACE)
            return NO_WIN;
    }
    return DRAW;
}

static void EndGame(int result)
{
    DrawEndGame(result);
    //ConnectToAWS();
    SendToAWS(result);
    while(1)
    {
        // block
    }
}

//*****************************************************************************
//
//! \brief The Function Handles WLAN Events
//!
//! \param[in]  pWlanEvent - Pointer to WLAN Event Info
//!
//! \return None
//!
//*****************************************************************************
void SimpleLinkWlanEventHandler(SlWlanEvent_t *pWlanEvent) {
    if(!pWlanEvent) {
        return;
    }

    switch(pWlanEvent->Event) {
        case SL_WLAN_CONNECT_EVENT: {
            SET_STATUS_BIT(g_ulStatus, STATUS_BIT_CONNECTION);

            //
            // Information about the connected AP (like name, MAC etc) will be
            // available in 'slWlanConnectAsyncResponse_t'.
            // Applications can use it if required
            //
            //  slWlanConnectAsyncResponse_t *pEventData = NULL;
            // pEventData = &pWlanEvent->EventData.STAandP2PModeWlanConnected;
            //

            // Copy new connection SSID and BSSID to global parameters
            memcpy(g_ucConnectionSSID,pWlanEvent->EventData.
                   STAandP2PModeWlanConnected.ssid_name,
                   pWlanEvent->EventData.STAandP2PModeWlanConnected.ssid_len);
            memcpy(g_ucConnectionBSSID,
                   pWlanEvent->EventData.STAandP2PModeWlanConnected.bssid,
                   SL_BSSID_LENGTH);

            UART_PRINT("[WLAN EVENT] STA Connected to the AP: %s , "
                       "BSSID: %x:%x:%x:%x:%x:%x\n\r",
                       g_ucConnectionSSID,g_ucConnectionBSSID[0],
                       g_ucConnectionBSSID[1],g_ucConnectionBSSID[2],
                       g_ucConnectionBSSID[3],g_ucConnectionBSSID[4],
                       g_ucConnectionBSSID[5]);
        }
        break;

        case SL_WLAN_DISCONNECT_EVENT: {
            slWlanConnectAsyncResponse_t*  pEventData = NULL;

            CLR_STATUS_BIT(g_ulStatus, STATUS_BIT_CONNECTION);
            CLR_STATUS_BIT(g_ulStatus, STATUS_BIT_IP_AQUIRED);

            pEventData = &pWlanEvent->EventData.STAandP2PModeDisconnected;

            // If the user has initiated 'Disconnect' request,
            //'reason_code' is SL_USER_INITIATED_DISCONNECTION
            if(SL_USER_INITIATED_DISCONNECTION == pEventData->reason_code) {
                UART_PRINT("[WLAN EVENT]Device disconnected from the AP: %s,"
                    "BSSID: %x:%x:%x:%x:%x:%x on application's request \n\r",
                           g_ucConnectionSSID,g_ucConnectionBSSID[0],
                           g_ucConnectionBSSID[1],g_ucConnectionBSSID[2],
                           g_ucConnectionBSSID[3],g_ucConnectionBSSID[4],
                           g_ucConnectionBSSID[5]);
            }
            else {
                UART_PRINT("[WLAN ERROR]Device disconnected from the AP AP: %s, "
                           "BSSID: %x:%x:%x:%x:%x:%x on an ERROR..!! \n\r",
                           g_ucConnectionSSID,g_ucConnectionBSSID[0],
                           g_ucConnectionBSSID[1],g_ucConnectionBSSID[2],
                           g_ucConnectionBSSID[3],g_ucConnectionBSSID[4],
                           g_ucConnectionBSSID[5]);
            }
            memset(g_ucConnectionSSID,0,sizeof(g_ucConnectionSSID));
            memset(g_ucConnectionBSSID,0,sizeof(g_ucConnectionBSSID));
        }
        break;

        default: {
            UART_PRINT("[WLAN EVENT] Unexpected event [0x%x]\n\r",
                       pWlanEvent->Event);
        }
        break;
    }
}

//*****************************************************************************
//
//! \brief This function handles network events such as IP acquisition, IP
//!           leased, IP released etc.
//!
//! \param[in]  pNetAppEvent - Pointer to NetApp Event Info
//!
//! \return None
//!
//*****************************************************************************
void SimpleLinkNetAppEventHandler(SlNetAppEvent_t *pNetAppEvent) {
    if(!pNetAppEvent) {
        return;
    }

    switch(pNetAppEvent->Event) {
        case SL_NETAPP_IPV4_IPACQUIRED_EVENT: {
            SlIpV4AcquiredAsync_t *pEventData = NULL;

            SET_STATUS_BIT(g_ulStatus, STATUS_BIT_IP_AQUIRED);

            //Ip Acquired Event Data
            pEventData = &pNetAppEvent->EventData.ipAcquiredV4;

            //Gateway IP address
            g_ulGatewayIP = pEventData->gateway;

            UART_PRINT("[NETAPP EVENT] IP Acquired: IP=%d.%d.%d.%d , "
                       "Gateway=%d.%d.%d.%d\n\r",
            SL_IPV4_BYTE(pNetAppEvent->EventData.ipAcquiredV4.ip,3),
            SL_IPV4_BYTE(pNetAppEvent->EventData.ipAcquiredV4.ip,2),
            SL_IPV4_BYTE(pNetAppEvent->EventData.ipAcquiredV4.ip,1),
            SL_IPV4_BYTE(pNetAppEvent->EventData.ipAcquiredV4.ip,0),
            SL_IPV4_BYTE(pNetAppEvent->EventData.ipAcquiredV4.gateway,3),
            SL_IPV4_BYTE(pNetAppEvent->EventData.ipAcquiredV4.gateway,2),
            SL_IPV4_BYTE(pNetAppEvent->EventData.ipAcquiredV4.gateway,1),
            SL_IPV4_BYTE(pNetAppEvent->EventData.ipAcquiredV4.gateway,0));
        }
        break;

        default: {
            UART_PRINT("[NETAPP EVENT] Unexpected event [0x%x] \n\r",
                       pNetAppEvent->Event);
        }
        break;
    }
}


//*****************************************************************************
//
//! \brief This function handles HTTP server events
//!
//! \param[in]  pServerEvent - Contains the relevant event information
//! \param[in]    pServerResponse - Should be filled by the user with the
//!                                      relevant response information
//!
//! \return None
//!
//****************************************************************************
void SimpleLinkHttpServerCallback(SlHttpServerEvent_t *pHttpEvent, SlHttpServerResponse_t *pHttpResponse) {
    // Unused in this application
}

//*****************************************************************************
//
//! \brief This function handles General Events
//!
//! \param[in]     pDevEvent - Pointer to General Event Info
//!
//! \return None
//!
//*****************************************************************************
void SimpleLinkGeneralEventHandler(SlDeviceEvent_t *pDevEvent) {
    if(!pDevEvent) {
        return;
    }

    //
    // Most of the general errors are not FATAL are are to be handled
    // appropriately by the application
    //
    UART_PRINT("[GENERAL EVENT] - ID=[%d] Sender=[%d]\n\n",
               pDevEvent->EventData.deviceEvent.status,
               pDevEvent->EventData.deviceEvent.sender);
}


//*****************************************************************************
//
//! This function handles socket events indication
//!
//! \param[in]      pSock - Pointer to Socket Event Info
//!
//! \return None
//!
//*****************************************************************************
void SimpleLinkSockEventHandler(SlSockEvent_t *pSock) {
    if(!pSock) {
        return;
    }

    switch( pSock->Event ) {
        case SL_SOCKET_TX_FAILED_EVENT:
            switch( pSock->socketAsyncEvent.SockTxFailData.status) {
                case SL_ECLOSE: 
                    UART_PRINT("[SOCK ERROR] - close socket (%d) operation "
                                "failed to transmit all queued packets\n\n", 
                                    pSock->socketAsyncEvent.SockTxFailData.sd);
                    break;
                default: 
                    UART_PRINT("[SOCK ERROR] - TX FAILED  :  socket %d , reason "
                                "(%d) \n\n",
                                pSock->socketAsyncEvent.SockTxFailData.sd, pSock->socketAsyncEvent.SockTxFailData.status);
                  break;
            }
            break;

        default:
            UART_PRINT("[SOCK EVENT] - Unexpected Event [%x0x]\n\n",pSock->Event);
          break;
    }
}

//*****************************************************************************
//
//! \brief This function initializes the application variables
//!
//! \param    0 on success else error code
//!
//! \return None
//!
//*****************************************************************************
static long InitializeAppVariables() {
    g_ulStatus = 0;
    g_ulGatewayIP = 0;
    g_Host = SERVER_NAME;
    memset(g_ucConnectionSSID,0,sizeof(g_ucConnectionSSID));
    memset(g_ucConnectionBSSID,0,sizeof(g_ucConnectionBSSID));
    return SUCCESS;
}


//*****************************************************************************
//! \brief This function puts the device in its default state. It:
//!           - Set the mode to STATION
//!           - Configures connection policy to Auto and AutoSmartConfig
//!           - Deletes all the stored profiles
//!           - Enables DHCP
//!           - Disables Scan policy
//!           - Sets Tx power to maximum
//!           - Sets power policy to normal
//!           - Unregister mDNS services
//!           - Remove all filters
//!
//! \param   none
//! \return  On success, zero is returned. On error, negative is returned
//*****************************************************************************
static long ConfigureSimpleLinkToDefaultState() {
    SlVersionFull   ver = {0};
    _WlanRxFilterOperationCommandBuff_t  RxFilterIdMask = {0};

    unsigned char ucVal = 1;
    unsigned char ucConfigOpt = 0;
    unsigned char ucConfigLen = 0;
    unsigned char ucPower = 0;

    long lRetVal = -1;
    long lMode = -1;

    lMode = sl_Start(0, 0, 0);
    ASSERT_ON_ERROR(lMode);

    // If the device is not in station-mode, try configuring it in station-mode 
    if (ROLE_STA != lMode) {
        if (ROLE_AP == lMode) {
            // If the device is in AP mode, we need to wait for this event 
            // before doing anything 
            while(!IS_IP_ACQUIRED(g_ulStatus)) {
#ifndef SL_PLATFORM_MULTI_THREADED
              _SlNonOsMainLoopTask(); 
#endif
            }
        }

        // Switch to STA role and restart 
        lRetVal = sl_WlanSetMode(ROLE_STA);
        ASSERT_ON_ERROR(lRetVal);

        lRetVal = sl_Stop(0xFF);
        ASSERT_ON_ERROR(lRetVal);

        lRetVal = sl_Start(0, 0, 0);
        ASSERT_ON_ERROR(lRetVal);

        // Check if the device is in station again 
        if (ROLE_STA != lRetVal) {
            // We don't want to proceed if the device is not coming up in STA-mode 
            return DEVICE_NOT_IN_STATION_MODE;
        }
    }
    
    // Get the device's version-information
    ucConfigOpt = SL_DEVICE_GENERAL_VERSION;
    ucConfigLen = sizeof(ver);
    lRetVal = sl_DevGet(SL_DEVICE_GENERAL_CONFIGURATION, &ucConfigOpt, 
                                &ucConfigLen, (unsigned char *)(&ver));
    ASSERT_ON_ERROR(lRetVal);
    
    UART_PRINT("Host Driver Version: %s\n\r",SL_DRIVER_VERSION);
    UART_PRINT("Build Version %d.%d.%d.%d.31.%d.%d.%d.%d.%d.%d.%d.%d\n\r",
    ver.NwpVersion[0],ver.NwpVersion[1],ver.NwpVersion[2],ver.NwpVersion[3],
    ver.ChipFwAndPhyVersion.FwVersion[0],ver.ChipFwAndPhyVersion.FwVersion[1],
    ver.ChipFwAndPhyVersion.FwVersion[2],ver.ChipFwAndPhyVersion.FwVersion[3],
    ver.ChipFwAndPhyVersion.PhyVersion[0],ver.ChipFwAndPhyVersion.PhyVersion[1],
    ver.ChipFwAndPhyVersion.PhyVersion[2],ver.ChipFwAndPhyVersion.PhyVersion[3]);

    // Set connection policy to Auto + SmartConfig 
    //      (Device's default connection policy)
    lRetVal = sl_WlanPolicySet(SL_POLICY_CONNECTION, 
                                SL_CONNECTION_POLICY(1, 0, 0, 0, 1), NULL, 0);
    ASSERT_ON_ERROR(lRetVal);

    // Remove all profiles
    lRetVal = sl_WlanProfileDel(0xFF);
    ASSERT_ON_ERROR(lRetVal);

    

    //
    // Device in station-mode. Disconnect previous connection if any
    // The function returns 0 if 'Disconnected done', negative number if already
    // disconnected Wait for 'disconnection' event if 0 is returned, Ignore 
    // other return-codes
    //
    lRetVal = sl_WlanDisconnect();
    if(0 == lRetVal) {
        // Wait
        while(IS_CONNECTED(g_ulStatus)) {
#ifndef SL_PLATFORM_MULTI_THREADED
              _SlNonOsMainLoopTask(); 
#endif
        }
    }

    // Enable DHCP client
    lRetVal = sl_NetCfgSet(SL_IPV4_STA_P2P_CL_DHCP_ENABLE,1,1,&ucVal);
    ASSERT_ON_ERROR(lRetVal);

    // Disable scan
    ucConfigOpt = SL_SCAN_POLICY(0);
    lRetVal = sl_WlanPolicySet(SL_POLICY_SCAN , ucConfigOpt, NULL, 0);
    ASSERT_ON_ERROR(lRetVal);

    // Set Tx power level for station mode
    // Number between 0-15, as dB offset from max power - 0 will set max power
    ucPower = 0;
    lRetVal = sl_WlanSet(SL_WLAN_CFG_GENERAL_PARAM_ID, 
            WLAN_GENERAL_PARAM_OPT_STA_TX_POWER, 1, (unsigned char *)&ucPower);
    ASSERT_ON_ERROR(lRetVal);

    // Set PM policy to normal
    lRetVal = sl_WlanPolicySet(SL_POLICY_PM , SL_NORMAL_POLICY, NULL, 0);
    ASSERT_ON_ERROR(lRetVal);

    // Unregister mDNS services
    lRetVal = sl_NetAppMDNSUnRegisterService(0, 0);
    ASSERT_ON_ERROR(lRetVal);

    // Remove  all 64 filters (8*8)
    memset(RxFilterIdMask.FilterIdMask, 0xFF, 8);
    lRetVal = sl_WlanRxFilterSet(SL_REMOVE_RX_FILTER, (_u8 *)&RxFilterIdMask,
                       sizeof(_WlanRxFilterOperationCommandBuff_t));
    ASSERT_ON_ERROR(lRetVal);

    lRetVal = sl_Stop(SL_STOP_TIMEOUT);
    ASSERT_ON_ERROR(lRetVal);

    InitializeAppVariables();
    
    return lRetVal; // Success
}



//****************************************************************************
//
//! \brief Connecting to a WLAN Accesspoint
//!
//!  This function connects to the required AP (SSID_NAME) with Security
//!  parameters specified in te form of macros at the top of this file
//!
//! \param  None
//!
//! \return  0 on success else error code
//!
//! \warning    If the WLAN connection fails or we don't aquire an IP
//!            address, It will be stuck in this function forever.
//
//****************************************************************************
static long WlanConnect() {
    SlSecParams_t secParams = {0};
    long lRetVal = 0;

    secParams.Key = SECURITY_KEY;
    secParams.KeyLen = strlen(SECURITY_KEY);
    secParams.Type = SECURITY_TYPE;

    UART_PRINT("Attempting connection to access point: ");
    UART_PRINT(SSID_NAME);
    UART_PRINT("... ...");
    lRetVal = sl_WlanConnect(SSID_NAME, strlen(SSID_NAME), 0, &secParams, 0);
    ASSERT_ON_ERROR(lRetVal);

    UART_PRINT(" Connected!!!\n\r");


    // Wait for WLAN Event
    while((!IS_CONNECTED(g_ulStatus)) || (!IS_IP_ACQUIRED(g_ulStatus))) {
        // Toggle LEDs to Indicate Connection Progress
        _SlNonOsMainLoopTask();
        GPIO_IF_LedOff(MCU_IP_ALLOC_IND);
        MAP_UtilsDelay(800000);
        _SlNonOsMainLoopTask();
        GPIO_IF_LedOn(MCU_IP_ALLOC_IND);
        MAP_UtilsDelay(800000);
    }

    return SUCCESS;

}

//*****************************************************************************
//
//! This function updates the date and time of CC3200.
//!
//! \param None
//!
//! \return
//!     0 for success, negative otherwise
//!
//*****************************************************************************

static int set_time() {
    long retVal;

    g_time.tm_day = DATE;
    g_time.tm_mon = MONTH;
    g_time.tm_year = YEAR;
    g_time.tm_sec = HOUR;
    g_time.tm_hour = MINUTE;
    g_time.tm_min = SECOND;

    retVal = sl_DevSet(SL_DEVICE_GENERAL_CONFIGURATION,
                          SL_DEVICE_GENERAL_CONFIGURATION_DATE_TIME,
                          sizeof(SlDateTime),(unsigned char *)(&g_time));

    ASSERT_ON_ERROR(retVal);
    return SUCCESS;
}

long printErrConvenience(char * msg, long retVal) {
    UART_PRINT(msg);
    GPIO_IF_LedOn(MCU_RED_LED_GPIO);
    return retVal;
}

//*****************************************************************************
//
//! This function demonstrates how certificate can be used with SSL.
//! The procedure includes the following steps:
//! 1) connect to an open AP
//! 2) get the server name via a DNS request
//! 3) define all socket options and point to the CA certificate
//! 4) connect to the server via TCP
//!
//! \param None
//!
//! \return  0 on success else error code
//! \return  LED1 is turned solid in case of success
//!    LED2 is turned solid in case of failure
//!
//*****************************************************************************
static int tls_connect() {
    SlSockAddrIn_t    Addr;
    int    iAddrSize;
    unsigned char    ucMethod = SL_SO_SEC_METHOD_TLSV1_2;
    unsigned int uiIP,uiCipher = SL_SEC_MASK_TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA;
    long lRetVal = -1;
    int iSockID;

    lRetVal = sl_NetAppDnsGetHostByName(g_Host, strlen((const char *)g_Host),
                                    (unsigned long*)&uiIP, SL_AF_INET);

    if(lRetVal < 0) {
        return printErrConvenience("Device couldn't retrieve the host name \n\r", lRetVal);
    }

    Addr.sin_family = SL_AF_INET;
    Addr.sin_port = sl_Htons(GOOGLE_DST_PORT);
    Addr.sin_addr.s_addr = sl_Htonl(uiIP);
    iAddrSize = sizeof(SlSockAddrIn_t);
    //
    // opens a secure socket 
    //
    iSockID = sl_Socket(SL_AF_INET,SL_SOCK_STREAM, SL_SEC_SOCKET);
    if( iSockID < 0 ) {
        return printErrConvenience("Device unable to create secure socket \n\r", lRetVal);
    }

    //
    // configure the socket as TLS1.2
    //
    lRetVal = sl_SetSockOpt(iSockID, SL_SOL_SOCKET, SL_SO_SECMETHOD, &ucMethod,\
                               sizeof(ucMethod));
    if(lRetVal < 0) {
        return printErrConvenience("Device couldn't set socket options \n\r", lRetVal);
    }
    //
    //configure the socket as ECDHE RSA WITH AES256 CBC SHA
    //
    lRetVal = sl_SetSockOpt(iSockID, SL_SOL_SOCKET, SL_SO_SECURE_MASK, &uiCipher,\
                           sizeof(uiCipher));
    if(lRetVal < 0) {
        return printErrConvenience("Device couldn't set socket options \n\r", lRetVal);
    }

    //
    //configure the socket with CA certificate - for server verification
    //
    lRetVal = sl_SetSockOpt(iSockID, SL_SOL_SOCKET, \
                           SL_SO_SECURE_FILES_CA_FILE_NAME, \
                           SL_SSL_CA_CERT, \
                           strlen(SL_SSL_CA_CERT));

    if(lRetVal < 0) {
        return printErrConvenience("Device couldn't set socket options \n\r", lRetVal);
    }

    //configure the socket with Client Certificate - for server verification
    //
    lRetVal = sl_SetSockOpt(iSockID, SL_SOL_SOCKET, \
                SL_SO_SECURE_FILES_CERTIFICATE_FILE_NAME, \
                                    SL_SSL_CLIENT, \
                           strlen(SL_SSL_CLIENT));

    if(lRetVal < 0) {
        return printErrConvenience("Device couldn't set socket options \n\r", lRetVal);
    }

    //configure the socket with Private Key - for server verification
    //
    lRetVal = sl_SetSockOpt(iSockID, SL_SOL_SOCKET, \
            SL_SO_SECURE_FILES_PRIVATE_KEY_FILE_NAME, \
            SL_SSL_PRIVATE, \
                           strlen(SL_SSL_PRIVATE));

    if(lRetVal < 0) {
        return printErrConvenience("Device couldn't set socket options \n\r", lRetVal);
    }


    /* connect to the peer device - Google server */
    lRetVal = sl_Connect(iSockID, ( SlSockAddr_t *)&Addr, iAddrSize);

    if(lRetVal < 0) {
        UART_PRINT("Device couldn't connect to server:");
        UART_PRINT(SERVER_NAME);
        UART_PRINT("\n\r");
        return printErrConvenience("Device couldn't connect to server \n\r", lRetVal);
    }
    else {
        UART_PRINT("Device has connected to the website:");
        UART_PRINT(SERVER_NAME);
        UART_PRINT("\n\r");
    }

    GPIO_IF_LedOff(MCU_RED_LED_GPIO);
    GPIO_IF_LedOn(MCU_GREEN_LED_GPIO);
    return iSockID;
}

int connectToAccessPoint() {
    long lRetVal = -1;
    GPIO_IF_LedConfigure(LED1|LED3);

    GPIO_IF_LedOff(MCU_RED_LED_GPIO);
    GPIO_IF_LedOff(MCU_GREEN_LED_GPIO);

    lRetVal = InitializeAppVariables();
    ASSERT_ON_ERROR(lRetVal);

    //
    // Following function configure the device to default state by cleaning
    // the persistent settings stored in NVMEM (viz. connection profiles &
    // policies, power policy etc)
    //
    // Applications may choose to skip this step if the developer is sure
    // that the device is in its default state at start of applicaton
    //
    // Note that all profiles and persistent settings that were done on the
    // device will be lost
    //
    lRetVal = ConfigureSimpleLinkToDefaultState();
    if(lRetVal < 0) {
      if (DEVICE_NOT_IN_STATION_MODE == lRetVal)
          UART_PRINT("Failed to configure the device in its default state \n\r");

      return lRetVal;
    }

    UART_PRINT("Device is configured in default state \n\r");

    CLR_STATUS_BIT_ALL(g_ulStatus);

    ///
    // Assumption is that the device is configured in station mode already
    // and it is in its default state
    //
    UART_PRINT("Opening sl_start\n\r");
    lRetVal = sl_Start(0, 0, 0);
    if (lRetVal < 0 || ROLE_STA != lRetVal) {
        UART_PRINT("Failed to start the device \n\r");
        return lRetVal;
    }

    UART_PRINT("Device started as STATION \n\r");

    //
    //Connecting to WLAN AP
    //
    lRetVal = WlanConnect();
    if(lRetVal < 0) {
        UART_PRINT("Failed to establish connection w/ an AP \n\r");
        GPIO_IF_LedOn(MCU_RED_LED_GPIO);
        return lRetVal;
    }

    UART_PRINT("Connection established w/ AP and IP is aquired \n\r");
    return 0;
}

void main() {
    //What the hell am I doing
//    char *addrToEdit = (char*)0xE000E008;
//    *addrToEdit = (*addrToEdit | 2);

    //Set up global variables
    edge_count = 0;
    DATA1[0] = '\0';
    DATA2[0] = '\0';

    // Initialize board configuration
    BoardInit();
    PinMuxConfig();
    SPIInit();
    OLEDInit();
    GPIOInit();
    //TimersInit();
    //UARTInit();
    TicTacToeInit();

    InitTerm();
    ClearTerm();
    UART_PRINT("My terminal works!\n\r");


    long lRetVal;
    //Connect the CC3200 to the local access point
    lRetVal = connectToAccessPoint();
    //Set time so that encryption can be used
    lRetVal = set_time();
    if(lRetVal < 0) {
        UART_PRINT("Unable to set time in the device");
        LOOP_FOREVER();
    }
    //Connect to the website with TLS encryption
    lRetVal = tls_connect();
    if(lRetVal < 0) {
        ERR_PRINT(lRetVal);
    }
    mainLRetVal = lRetVal;



    //Update shadow to clean board
    //SendToAWS();
    //http_get(mainLRetVal);
    //UART_PRINT("*****DONE*****\n\r");

//    UART_PRINT("*****GET?*****\n\r");
//    http_get(mainLRetVal); //do we need to GET before doing anything?
//    UART_PRINT("*****GET!*****\n\r");

    //Start timer
    //Timer_IF_Start(get_base, TIMER_A, GET_REQUEST_CHECK_MS);
    while(1){
    }

    //http_post(lRetVal);
    //sl_Stop(SL_STOP_TIMEOUT);
    //LOOP_FOREVER();
}
//*****************************************************************************
//
// Close the Doxygen group.
//! @}
//
//*****************************************************************************

static int http_post(int iTLSSockID){
    char acSendBuff[512];
    char acRecvbuff[1460];
    char cCLLength[200];
    char* pcBufHeaders;
    int lRetVal = 0;

    pcBufHeaders = acSendBuff;
    strcpy(pcBufHeaders, POSTHEADER);
    pcBufHeaders += strlen(POSTHEADER);
    strcpy(pcBufHeaders, HOSTHEADER);
    pcBufHeaders += strlen(HOSTHEADER);
    strcpy(pcBufHeaders, CHEADER);
    pcBufHeaders += strlen(CHEADER);
    strcpy(pcBufHeaders, "\r\n\r\n");

    int dataLength = strlen(DATA1);

    strcpy(pcBufHeaders, CTHEADER);
    pcBufHeaders += strlen(CTHEADER);
    strcpy(pcBufHeaders, CLHEADER1);

    pcBufHeaders += strlen(CLHEADER1);
    sprintf(cCLLength, "%d", dataLength);

    strcpy(pcBufHeaders, cCLLength);
    pcBufHeaders += strlen(cCLLength);
    strcpy(pcBufHeaders, CLHEADER2);
    pcBufHeaders += strlen(CLHEADER2);

    strcpy(pcBufHeaders, DATA1);
    pcBufHeaders += strlen(DATA1);

    int testDataLength = strlen(pcBufHeaders);

    UART_PRINT(acSendBuff);


    //
    // Send the packet to the server */
    //
    lRetVal = sl_Send(iTLSSockID, acSendBuff, strlen(acSendBuff), 0);
    if(lRetVal < 0) {
        UART_PRINT("POST failed. Error Number: %i\n\r",lRetVal);
        sl_Close(iTLSSockID);
        GPIO_IF_LedOn(MCU_RED_LED_GPIO);
        return lRetVal;
    }
    lRetVal = sl_Recv(iTLSSockID, &acRecvbuff[0], sizeof(acRecvbuff), 0);
    if(lRetVal < 0) {
        UART_PRINT("Received failed. Error Number: %i\n\r",lRetVal);
        //sl_Close(iSSLSockID);
        GPIO_IF_LedOn(MCU_RED_LED_GPIO);
           return lRetVal;
    }
    else {
        acRecvbuff[lRetVal+1] = '\0';
        UART_PRINT(acRecvbuff);
        UART_PRINT("\n\r\n\r");
    }

    return 0;
}


static int http_get(int iTLSSockID){
    char acSendBuff[512];
    char acRecvbuff[1460];
    char* pcBufHeaders;
    int lRetVal = 0;

    pcBufHeaders = acSendBuff;
    strcpy(pcBufHeaders, GETHEADER);
    pcBufHeaders += strlen(GETHEADER);
    strcpy(pcBufHeaders, HOSTHEADER);
    pcBufHeaders += strlen(HOSTHEADER);
    strcpy(pcBufHeaders, CHEADER);
    pcBufHeaders += strlen(CHEADER);
    strcpy(pcBufHeaders, "\r\n\r\n");

    int testDataLength = strlen(pcBufHeaders);

    UART_PRINT(acSendBuff);


    //
    // Send the packet to the server */
    //
    lRetVal = sl_Send(iTLSSockID, acSendBuff, strlen(acSendBuff), 0);
    if(lRetVal < 0) {
        UART_PRINT("GET failed. Error Number: %i\n\r",lRetVal);
        sl_Close(iTLSSockID);
        GPIO_IF_LedOn(MCU_RED_LED_GPIO);
        return lRetVal;
    }
    lRetVal = sl_Recv(iTLSSockID, &acRecvbuff[0], sizeof(acRecvbuff), 0);
    if(lRetVal < 0) {
        UART_PRINT("Received failed. Error Number: %i\n\r",lRetVal);
        //sl_Close(iSSLSockID);
        GPIO_IF_LedOn(MCU_RED_LED_GPIO);
           return lRetVal;
    }
    else {
        acRecvbuff[lRetVal+1] = '\0';
        UART_PRINT(acRecvbuff);
        UART_PRINT("\n\r\n\r");
    }

    strcpy(&DATA2[0], acRecvbuff);

    return 0;
}
