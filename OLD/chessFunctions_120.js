/*
* TanKy Mobil Chess by tomitank
* Date:2017.09.28.
* Author:tomitank [Kuzmics Tamas]
* Contact:tomitank@freemail.hu , tanky.hu@gmail.com
* [^:]//.* regular search->comment del
*/

	var premium = 'yes'; // premium
	var verzio = '2.1.9'; // verzio
	var musicOff = false; // zene ?
	var soundOff = false; // hang ?
	var globalSound = null; // hang
	var helpLoop = false; // segit?
	var DRAG_DIV = null; // Drag div
	var appPaused = false; // szunet?
	var onMoveLoop = false; // lepes?
	var vibrateOff = false; // rezeg?
	var EPAlertOff = false; //EPAlert
	var cordova_js = false; // cordova
	var nativeAudio = false; // plugin
	var gameMode = 1; // gep vagy 1v1
	var yourSide = 0; // Feherrel kezd
	var LanguageReady = 0; // Nyelv ok?
	var menuAnim = false; // animacio ?
	var anim_diff_1 = ''; // animacio 1
	var anim_diff_2 = ''; // animacio 2
	var anim_diff_3 = ''; // animacio 3
	var BABU_STYLE = ''; // Babu kinezet
	var brd_bookLines = []; // Open book
	var rotatePiece = true; // Babuforgatas
	var koordinateOff = false; // Koordinatak
	var clickEventType = ''; // click or touch
	var WorkerSearch = null; // Kereseshez timer
	var backgroundEngine = null; // Worker Enginge
	var backgroundEngineValid = true; // Worker ok?
	var BOARD_COLOR = 'default_image'; // Tabla szin
	var JATEK_FOLYAMATBAN = true; // jatek folyamatban ?
	var ALPHA_BETA_MAX_IDO = 2000; // maximalis vizsgalati ido (ms)
	var START_FEN = 'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 0'; // Kezdo FEN
	var updateUrl = 'https://itunes.apple.com/us/app/sakk/id1152837781?l=hu&ls=1&mt=8'; // Frissites link
	var gep_szint = { 100 : 1, 200 : 2, 300 : 3, 1000 : 4, 2000 : 5, 4000 : 6, 8000 : 7, 15000 : 8, 30000 : 9 }; // Szintek


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// HTML betoltodott
		$(document).ready(function() {

		// Forditas betoltese (translate/hu.js mar betoltve)
			getTranslate('device', false);

		// Nyitas konyv betoltese
			$.ajax({
				cache : false,
				mimeType: "text/plain",
				url : "sakk_openBook.txt",
				success: function (txt) {
					$(txt).find('line').each(function() {
						var trimmed = $(this).text();
						trimmed = $.trim(trimmed);
						brd_bookLines.push(trimmed);
					});
				}
			});

		// Aminamciok deffinialasa
			anim_diff_1 = $('#main').width(); // 1. animacio differencia
			anim_diff_2 = (anim_diff_1 * 2); // 2. animacio differencia
			anim_diff_3 = (anim_diff_1 * 3); // 3. animacio differencia

		// DIV elemek dinamikus allitasa
			var logoHeight = $('#logo').height(); // logo magassag
			var mainHeight = $('#main').height(); // main div magassag
			var newTextHeight = (mainHeight - logoHeight - 68); // szoveges div uj magassaga
			$('#stat_content').css({'max-height': (newTextHeight - 55)}); // statisztika div dinamikus beallitasa
			$('#about_content, #rules_content').css({'max-height': newTextHeight}); // szoveges div dinamikus beallitasa

		// Kattintas vagy erintes
			clickEventType = ((document.ontouchstart !== null) ? 'click' : 'touchstart');

		// Status bar eltuntetese
			$('*').on(clickEventType, function() {
				if (cordova_js) StatusBar.hide(); // betoltodott a cordova.js
			});

		// Erosseg allitasakor
			$(document).on('input', '#erossegek', function() {
				var value = parseInt($(this).val());
				$('#aktualis_erosseg').html(value);
				Gep_Erosseg(Object.keys(gep_szint)[value-1], false);
			});

		// Link background "data" parameterbe mentese mobilon
			if (clickEventType == 'touchstart') {
				$('a').each(function() {
					var back_color = $(this).css('background-color');
					var background = $(this).css('background');
					$(this).attr('data-back_color', back_color);
					$(this).attr('data-background', background);
				});
			}

		// Link a:hover torlese mobilon
			$('a').on('touchstart touchend', function(e) {
				if (e.type == 'touchstart') {
					$(this).attr('style', '');
				} else {
					var background = $(this).attr('data-background');
					var back_color = $(this).attr('data-back_color');
					if (back_color != undefined) {
						$(this).css({'background-color': back_color});
					}
					if (background != undefined) {
						$(this).css({'background': background});
					}
				}
			});

		// Hangok a gomboknal
			$('#game_buttons a, #game_options a, #game_side a, #game_board a, #game_pieces a, #game_rotatepiece a').on(clickEventType+' touchend', function(e) {
				if (e.type == 'click' || e.type == 'touchend') {
					if ($(this).parent().attr('id') != 'game_sound') {
						playAudio('button_click');
					}
				}
			});

		// Zene beallitas mentesbol
			if (window.localStorage.getItem("MUSIC_OFF")) {
				musicChange();
			}

		// Hang beallitas mentesbol
			if (window.localStorage.getItem("SOUND_OFF")) {
				soundChange();
			}

		// Rezges beallitas mentesbol
			if (window.localStorage.getItem("VIBRATE_OFF")) {
				vibrateChange();
			}

		// Koordinatak beallitas mentesbol
			if (window.localStorage.getItem("KOORDINATE_OFF")) {
				koordChange();
			}

		// En Passant jelzes mentesbol
			if (window.localStorage.getItem("EP_ALERT_OFF")) {
				EPAlertChange(1);
			}

		// Babuk elforgatasa (2 jatekos modban) 
			if (window.localStorage.getItem("BABUFORGATAS_OFF")) {
				rotatePieceChange();
			}

		// Erosseg beallitasa mentesbol
			if (window.localStorage.getItem("GEP_EROSSEG"))
			{
				ALPHA_BETA_MAX_IDO = parseInt(window.localStorage.getItem("GEP_EROSSEG"));

				if (gep_szint[ALPHA_BETA_MAX_IDO] != undefined) {
					$('#erossegek').val(gep_szint[ALPHA_BETA_MAX_IDO]);
					$('#aktualis_erosseg').html(gep_szint[ALPHA_BETA_MAX_IDO]);
				} else {
					ALPHA_BETA_MAX_IDO = 2000;
					$('#erossegek').val(gep_szint[ALPHA_BETA_MAX_IDO]);
					$('#aktualis_erosseg').html(gep_szint[ALPHA_BETA_MAX_IDO]);
				}
			}

		// Tabla szin beallitasa mentesbol
			if (window.localStorage.getItem("TABLA_SZIN")) {
				boardColor(window.localStorage.getItem("TABLA_SZIN"));
			}

		// Babu kinezet beallitasa mentesbol
			if (window.localStorage.getItem("BABU_STYLE")) {
				pieceStyle(window.localStorage.getItem("BABU_STYLE"));
			}

		// Ki kezdhet beallitasa mentesbol
			if (window.localStorage.getItem("KI_KEZDHET"))
			{
				yourSide = parseInt(window.localStorage.getItem("KI_KEZDHET"));

				if (yourSide === 8) // oldalvalto beallitasa a menube
				{
					$('#player_1_side').animate({'left': '+='+105}, 300, false); // feher oldal csere
					$('#player_2_side').animate({'right': '+='+105}, 300, false); // fekete oldal csere
				}
			}

		// "64 bitre" valo atallas miatt a regi jatekot toroljuk
			if (window.localStorage.getItem("SIDE_KEY")) {
				window.localStorage.removeItem("JATEK_MOD");
				window.localStorage.removeItem("MOVE_HISTORY");
				window.localStorage.removeItem("CASTLE_KEYS");
				window.localStorage.removeItem("PIECE_KEYS");
				window.localStorage.removeItem("SIDE_KEY");
				window.localStorage.removeItem("FEN");
			}

		// Ha volt elmentett jatek akkor folytatjuk
			if (window.localStorage.getItem("MOVE_HISTORY"))
			{
				MOVE_HISTORY = JSON.parse(window.localStorage.getItem("MOVE_HISTORY")); // Elozmenyek
				CastleKeysHigh = JSON.parse(window.localStorage.getItem("CASTLE_KEYS_HIGH")); // Sancolas hashKey
				CastleKeysLow = JSON.parse(window.localStorage.getItem("CASTLE_KEYS_LOW")); // Sancolas hashKey
				PieceKeysHigh = JSON.parse(window.localStorage.getItem("PIECE_KEYS_HIGH")); // Babuk hashKey
				PieceKeysLow = JSON.parse(window.localStorage.getItem("PIECE_KEYS_LOW")); // Babuk hashKey
				SideKeyHigh = parseInt(window.localStorage.getItem("SIDE_KEY_HIGH")); // Aki lephet hashKey
				SideKeyLow = parseInt(window.localStorage.getItem("SIDE_KEY_LOW")); // Aki lephet hashKey
				gameMode = parseInt(window.localStorage.getItem("JATEK_MOD")); // Jatekmod
				START_FEN = window.localStorage.getItem("FEN"); // FEN mentesbol

				var LAST_MOVE = MOVE_HISTORY[MOVE_HISTORY.length-1]; // Utolso lepes
				moveCount = parseInt(MOVE_HISTORY.length); // Lepesek szama
				brd_fiftyMove = LAST_MOVE.fiftyMove; // 50 lepes frissitese

				ChessEngineRestart(); // Sakk motor ujrainditas
				CHESS_BOARD = FENToBoard(); // Tabla feltoltese
				drawBoard(CHESS_BOARD, LAST_MOVE.move); // Tabla rajzolasa

				if (gameMode === 2) { // Segiseg gomb ki
					$('#game_help').addClass('hidden');
				} else if (currentPlayer != yourSide) { // Gep ellen
					setTimeout(function() { FindMove(0); }, 100); // Kereses
				}

				// EGYIDOBEN FUTNAK LE >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
				$('#content').animate({'margin-left': '-'+anim_diff_1, 'width': anim_diff_2}, 0, false); // content 2 ablak

				$('#game_between').animate({'width': '0px'}, 0, false, function() { // koztes menu >> 0px
					$('#logo').removeClass('menu_logo'); // logo oldalra kerul
					$('#welcome').css({'display':'none'}); // udvozles eltunik
					$('#game_resume').css({'display':'block'}); // folytatas gomb be
					$('#menu_button').css({'display':'block'}); // menu gomb megjelenitese
					$('#game_between').css({'display':'none', 'width': anim_diff_1}); // koztes menu ki + szelesseg novelese
				});
				// EGYIDOBEN FUTNAK LE >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			} else { // Nem volt megkezdett jatekunk

				InitHashKeys(); // HashKey inicializalas!
				InitEvalMasks(); // Bitmaszkok betoltese!
				InitPieceList(); // Babuk inicializalasa!
				GenerateHashKey(); // HashKey generalasa!
				drawBoard(CHESS_BOARD, NOMOVE); // Tabla rajzolasa

			}

			document.addEventListener("deviceready", onDeviceReady, false); // betoltodott a cordova.js

		});


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// global ertesito
		function global_info(html) {
			var wtop = (document.documentElement.clientHeight-312) / 2;
			var wleft = (document.documentElement.clientWidth-312) / 2;

			if (!wtop || !wleft || wtop <= 0 || wleft <= 0) { // BUGFIX
				var wtop = 10;
				var wleft = 10;
			}

			var end_html = '<div id="global_menu">';
			end_html += '<div id="global_menu_info">TanKy.hu Sakk</div>';
			end_html += '</div>';
			end_html += '<div class="clear"></div>';
			end_html += '<div id="global_info">'+html+'</div>';

		// Uzenet feltoltese, kiirasa
			$('#global_alert').html(end_html).css({'display': 'block', 'left': wleft, 'top': wtop});

		// Gyalog bevaltashoz
			$('.csere_babu').on(clickEventType, function() {
				var elem = $(this).attr('alt').split(',');
				return pawnPromotion(parseInt(elem[0]), parseInt(elem[1]), parseInt(elem[2]));
			});

		// Info linkre kattintas (.elfogad .ok_gomb .elutasit)
			$('.elfogad, .ok_gomb, .elutasit').on(clickEventType, function() {
				var link = $(this).attr('alt');
				if (link == 'global_info_close') {
					return setTimeout(function() { global_info_close(); }, 500);
				} else {
					return window.open(link, '_system');
				}
			});
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// global ertesito bezaras
		function global_info_close() {
			$('#global_alert').html('').css({'display': 'none'});
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// forditasi nyelv betoltese
		function getTranslate(id, user) {

			var saved = window.localStorage.getItem("SELECTED_LANGUAGE");
			var html_data = $('#game_languages').attr('data-language');

		// ------------------------------------------------------------------
		// 1. Inditaskor, ha mar van kivalasztott nyelv
		// ------------------------------------------------------------------
			if (id == 'device' && saved && user === false)
			{
				getTranslate(saved, false); // Mentett nyelv

				if (saved != html_data) { // Html frissites
					$('#game_languages').attr('data-language', saved);
					$('#game_languages a img').css({'display':'none'});
					$('div[data-language_id="'+saved+'"] img').css({'display':'block'});
				}
				return true;
			}
		// ------------------------------------------------------------------
		// 2. Automata, ha nincs mentes inditaskor, vagy menubol kivalasztva
		// ------------------------------------------------------------------
			if (id == 'device' && (!saved || user === true))
			{
				if (cordova_js && navigator.globalization !== undefined) // cordova.js
				{
					navigator.globalization.getPreferredLanguage(function (language) {
						if (language.value !== undefined && language.value != '') {
							if (language.value.substr(0, 2) == 'hu') {
								getTranslate('hu', false); // Magyar
							} else {
								getTranslate('en', false); // Angol
							}
							// Mentes torlese (Automata uzemmod)
							window.localStorage.removeItem("SELECTED_LANGUAGE");
							$('#game_languages a img').css({'display':'none'});
							$('#game_languages').attr('data-language', 'device');
							$('div[data-language_id="device"] img').css({'display':'block'});
						}
					});
				}
				else // Bongeszo
				{
					var userLang = navigator.language || navigator.userLanguage;
					if (userLang !== undefined && userLang.substr(0, 2) != '') {
						if (userLang.substr(0, 2) == 'hu') {
							getTranslate('hu', false); // Magyar
						} else {
							getTranslate('en', false); // Angol
						}
						// Mentes torlese (Automata uzemmod)
						window.localStorage.removeItem("SELECTED_LANGUAGE");
						$('#game_languages a img').css({'display':'none'});
						$('#game_languages').attr('data-language', 'device');
						$('div[data-language_id="device"] img').css({'display':'block'});
					}
				}
				return true;
			}
		// ------------------------------------------------------------------
		// 3. Nyelv betoltes (Ha nem egyezik)
		// ------------------------------------------------------------------
			if (id != LANGUAGE.language)
			{
			// Loader on
				global_info('<object type="image/svg+xml" data="pic/loader.svg">'
								+'<img src="pic/loader.gif">' // hiba eseten
							+'</object>');

			// Nyelvi fajl betoltese
				$.ajax({
					cache : false,
					dataType: "json",
					mimeType: "text/plain",
					url : "translate/"+id+".json",
					success: function (res) { // Kesz
						LANGUAGE = res;
						Translation();
						LanguageReady = 1;
						quietBoardUpdate();
						global_info_close();
					}, error: function () { // Hiba
						global_info_close();
					}
				});
			} else { LanguageReady = 1; } // Hack!!
		// ------------------------------------------------------------------
		// 4. Html frissites + mentes (Menubol)
		// ------------------------------------------------------------------
			if (id != html_data && user === true)
			{
				window.localStorage.setItem("SELECTED_LANGUAGE", id);
				$('#game_languages').attr('data-language', id);
				$('#game_languages a img').css({'display':'none'});
				$('div[data-language_id="'+id+'"] img').css({'display':'block'});
			}
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// HTML forditas az adott nyelvre
		function Translation() {
			if (LANGUAGE != 0) {
				for (var id in LANGUAGE) {
					if (id.substr(0, 1) != '#') continue; // Nem HTML
					var html_elem = $(id); // HTML elem Objektum
					if (html_elem.length != 0) // Letezo HTML elem
					{
						var str_id = -1; // Szoveg pozicioja
						// <div>Szoveg<img></div> -> Szoveg 0. pozicioban van
						// <div><img>Szoveg</div> -> Szoveg 1. pozicioban van
						html_elem.contents().filter(function(index)
						{
							if (this.nodeType === 3 && $.trim(this.data) !== '' && str_id === -1) {
								str_id = index; // Csak az elso tenyleges szoveget szabad cserelni!
							}
						});

						html_elem.contents().eq(str_id).replaceWith(LANGUAGE[id]); // Szoveg csere
					}
				}
			}
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// adatvedelmi nyilatkozat
		function privacyCheck() {
			if (!window.localStorage.getItem("PRIVACY")) {

				var TITLE	= LANGUAGE.policy_title;
				var MESSAGE = LANGUAGE.policy_message;
				var BUTTONS = [LANGUAGE.policy_button_1, LANGUAGE.policy_button_2, LANGUAGE.policy_button_3];

				navigator.notification.confirm(
					MESSAGE, // Uzenet
					function (gomb) { // Funkcio
						if (gomb == 1) {
							window.open('http://mobil.tanky.hu/privacy.html', '_system'); // Elolvas
							return privacyCheck();
						} else if (gomb == 2) {
							window.localStorage.setItem("PRIVACY", 1); // Elfogad
							return privacyCheck();
						} else if (gomb == 3) {
							navigator.app.exitApp(); // Kilepes
							return privacyCheck();
						} else {
							return privacyCheck(); // Mashova kattintas
						}
					},
					TITLE, // Cim
					BUTTONS // Gomb
				);
			}
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// cordova.js betoltodott
		function onDeviceReady() {

			cordova_js = true; // betoltodott a cordova
			StatusBar.hide(); // status bar eltuntetese
			navigator.splashscreen.hide(); // Kezdo kep eltuntetese

			if (window.plugins && window.plugins.NativeAudio) { // Hang plugin betoltve
				nativeAudio = true;
				loadMusic(); // Zene betoltese
				loadAudio(); // Hang betoltese
			}

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			getTranslate('device', false); // Forditas betoltese...

			var getLanguage = setInterval(function() { // Betoltes..
				if (LanguageReady != 0) { // Kesz
					clearInterval(getLanguage);
					privacyCheck(); // Adatvedelmi Nyilatkozat
				}
			}, 300);

			setTimeout(function() { // Vedelem 10s utan
				if (LanguageReady == 0) {
					clearInterval(getLanguage);
					alert('Nem sikerult betolteni a nyelvi fajlt!');
				}
			}, 10000);

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			document.addEventListener("pause", pauseApp, false); // Ha hatterbe kerul az alkalmazas
			document.addEventListener("resume", resumeApp, false); // Ha ujra fut az alkalmazas
			document.addEventListener("online", onOnline(true), false); // Ha van internet-kapcsolat
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// Az alkalmazassal kapcsolatos uzenet a felhasznalonak, ha van internetkapcsolat
		function onOnline(open) {

			if (parseInt(window.localStorage.getItem("LAST_ONLINE")) > Date.now()) { // 5 percen belul ne kuldje ujra
				return true;
			} else {
				window.localStorage.setItem("LAST_ONLINE", (Date.now() + (5 * 60000))); // Elmentjuk a mostani idot + 5 perc
			}

			if (verzio != window.localStorage.getItem("SAKK_VERZIO")) { // 1 verzioval 1x irunk a txt-be
				var ready = false;
				window.localStorage.setItem("SAKK_VERZIO", verzio); // Elmentjuk a mostani verziot
			} else {
				var ready = true;
			}

			$.ajax({
				type: "POST",
				url : "http://mobil.tanky.hu/appInfo/mobilAppInfo.php",
				cache : false,
				data: { "verzio": verzio,
						"zeneki": musicOff,
						"hangki": soundOff,
						"babuk": BABU_STYLE,
						"szinek": BOARD_COLOR,
						"rezegki": vibrateOff,
						"eszkoz": device.platform,
						"ready": (ready ? "yes" : "no"),
						"premium": premium, "open": (open ? "yes" : "no" ),
						"beststat": window.localStorage.getItem("best_stat")
				}, success: function (info) {
					if (info != '') {
						if (info.substr(0, 1) == '*') { // Info kozelese
							if ($('#global_alert').html() == '') { // Csak ha ures a box! (Gyalobevaltas)
								global_info(info.substr(1));
							}
						}
					}
				}
			});
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// Jatek megosztas
		function Game_Share(id) {
			if (!cordova_js) return false; // nem tudott betoltodni a cordova.js
			if (maxSearchTime != 0 || onMoveLoop) return false; // Kereses fut

			if (!id && !window.localStorage.getItem("SHARE_OFF")) // Leiras
			{
				navigator.notification.confirm(
					LANGUAGE.share_info, // Uzenet
					function(gomb) { // Funkcio
						if (gomb == 2) {
							window.localStorage.setItem("SHARE_OFF", 1);
						}
						Game_Share(1);
					},
					LANGUAGE.share_title, // Cim
					[LANGUAGE.yes_button, LANGUAGE.no_button] // Gomb
				);
			}
			else if (window.plugins && window.plugins.socialsharing) // Plugin betoltve
			{
				var date = (new Date()).toISOString().split('-').join('.');
				var message = '[Event "'+device.platform+' Game"]\n';
				message += '[Site "TanKy.HU Mobil Chess"]\n';
				message += '[Date "'+date.slice(0,10)+'"]\n';
				message += '[Round "?"]\n';
				if (gameMode == 1) {
					message += '[White "'+(yourSide ? 'Mobil ('+gep_szint[ALPHA_BETA_MAX_IDO]+')' : 'Player')+'"]\n';
					message += '[Black "'+(yourSide ? 'Player' : 'Mobil ('+gep_szint[ALPHA_BETA_MAX_IDO]+')')+'"]\n';
				} else {
					message += '[White "'+(yourSide ? '2.Player' : '1.Player')+'"]\n';
					message += '[Black "'+(yourSide ? '1.Player' : '2.Player')+'"]\n';
				}
				message += '[Result "?"]\n\n';

				//>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

				var CountMove = moveCount; // Atmenetni tarolo
				var HISTORY = MOVE_HISTORY; // Atmeneti tarolo
				while (moveCount > 0) { // Osszes lepes vissza
					unMakeMove();
				}

				ClearForSearch(); // Elozmeny nullazas

				//>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

				for (var index = 0; index < CountMove; index++) // Lepesek
				{
					var MOVE = HISTORY[index].move;
					var to = TOSQ(MOVE);
					var from = FROMSQ(MOVE);
					var pieceType = CHESS_BOARD[from] & 0x07;
					var toStr = $('div[data-square="'+to+'"]').attr('alt');
					var fromStr = $('div[data-square="'+from+'"]').attr('alt');

					if ((index+1) % 2 != 0) {
						message += index == 0 ? '' : ' ';
						message += Math.round((index+1)/2)+'. '; // Sorszam
					} else {
						message += ' ';
					}

					if (MOVE & CASTLED_MASK) { // Sancolas
						message += 'O-O';
						if (to == SQUARES.C1 || to == SQUARES.C8) {
							message += '-O';
						}
						makeMove(MOVE);
						continue;
					} else {
						message += ['', '', 'N', 'K', '', 'B', 'R', 'Q'][pieceType];
					}

					boardPly = 0; // Hack: boardPly overflow
					GenerateAllMoves(false, false); // Minden lepes
					var dupe = false, rowDiff = true, colDiff = true;

					for (var j = brd_moveStart[0]; j < brd_moveStart[1]; ++j)
					{
						var moveFound = brd_moveList[j];

						if (!makeMove(moveFound)) {
							continue;
						}
						unMakeMove();

						var moveTo = TOSQ(moveFound);
						var moveFrom = FROMSQ(moveFound);

						if (moveFrom != from && moveTo == to
						&& (CHESS_BOARD[moveFrom] & 0x07) == pieceType) { // Tobb babu
							dupe = true;
							if (TableRanks[moveFrom] == TableRanks[from]) {
								rowDiff = false;
							}
							if (TableFiles[moveFrom] == TableFiles[from]) {
								colDiff = false;
							}
						}
					}

					if (dupe) {
						if (colDiff) {
							message += fromStr.charAt(0);
						} else if (rowDiff) {
							message += fromStr.charAt(1);
						} else {
							message += fromStr;
						}
					} else if (pieceType === PAWN && (MOVE & CAPTURE_MASK)) { // Gyaloggal utes
						message += fromStr.charAt(0);
					}
					
					if (MOVE & CAPTURE_MASK) { // Utes
						message += 'x';
					}
					
					message += toStr; // Ahova leptunk

					if (PROMOTED(MOVE) != 0) // Gyalog bevaltas
					{
						message += ['', '', '=N', '', '', '=B', '=R', '=Q'][PROMOTED(MOVE) & 0x07];
					}

					makeMove(MOVE); // Lepes

					if (isCheck(currentPlayer)) { // Sakk
						if (index == CountMove-1 && !JATEK_FOLYAMATBAN) { // Matt
							message += '#';
						} else {
							message += '+';
						}
					}
				}

				//>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

				window.plugins.socialsharing.share( // Megosztas ablak
					message, // Uzenet
					'TanKy.HU Chess', // Cim
					null, // Kep
					null, // Fajl
					function() { return null; }, // OK
					function() { return null; } // NOK
				);
			}
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


    // Az alkalmazas a hatterben
		function pauseApp(status) {
			if (!cordova_js) return false; // nem tudott betoltodni a cordova.js

			appPaused = true; // az alkalmazas a hatterbe kerult
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


    // Az alkalmazas folytatasa
		function resumeApp() {
			if (!cordova_js) return false; // nem tudott betoltodni a cordova.js

			appPaused = false; // az alkalmazas ujra fut

			document.addEventListener("online", onOnline(false), false); // Ha van internet-kapcsolat

			StatusBar.hide(); // status bar eltuntetese
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// Zene torlese
		function unloadMusic() {
			if (nativeAudio === true) {
				window.plugins.NativeAudio.stop("music");
				window.plugins.NativeAudio.unload("music");
			}
		}
	// Zene betoltese
		function loadMusic() {
			if (nativeAudio === true && musicOff === false) {
				window.plugins.NativeAudio.preloadComplex("music", "sound/mozart.mp3", 1, 1, 0, function(msg) { // Zene inditasa
					window.plugins.NativeAudio.loop("music");
				}, function(msg) { // Mar be volt toltve
					window.plugins.NativeAudio.stop("music");
					window.plugins.NativeAudio.loop("music");
				});
			}
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// Hangok torlese
		function unloadAudio() {
			if (nativeAudio === true) {
				window.plugins.NativeAudio.unload("sakk_sakk");
				window.plugins.NativeAudio.unload("sakk_utes");
				window.plugins.NativeAudio.unload("game_egal");
				window.plugins.NativeAudio.unload("menu_slash");
				window.plugins.NativeAudio.unload("sakk_lepes");
				window.plugins.NativeAudio.unload("game_looser");
				window.plugins.NativeAudio.unload("game_winner");
				window.plugins.NativeAudio.unload("button_click");
			}
		}
	// Hangok betoltese
		function loadAudio(menu) {
			if (nativeAudio === true && soundOff === false) {
				window.plugins.NativeAudio.preloadComplex("sakk_sakk", "sound/sakk_sakk.mp3", 1, 1, 0, null, null);
				window.plugins.NativeAudio.preloadComplex("sakk_utes", "sound/sakk_utes.mp3", 1, 1, 0, null, null);
				window.plugins.NativeAudio.preloadComplex("game_egal", "sound/game_egal.mp3", 1, 1, 0, null, null);
				window.plugins.NativeAudio.preloadComplex("menu_slash", "sound/menu_slash.mp3", 1, 1, 0, null, null);
				window.plugins.NativeAudio.preloadComplex("sakk_lepes", "sound/sakk_lepes.mp3", 1, 1, 0, null, null);
				window.plugins.NativeAudio.preloadComplex("game_looser", "sound/game_looser.mp3", 1, 1, 0, null, null);
				window.plugins.NativeAudio.preloadComplex("game_winner", "sound/game_winner.mp3", 1, 1, 0, null, null);
				window.plugins.NativeAudio.preloadComplex("button_click", "sound/button_click.mp3", 1, 1, 0, function(msg) {
					if (menu) playAudio('button_click'); // Hang bekapcsolaskor
				}, function(msg) { // Mar be volt toltve
					if (menu) playAudio('button_click'); // Hang bekapcsolaskor
				});
			}
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// Hang lejatszas
		function playAudio(audio) {
			if (soundOff === true) return false; // ki van kapcsolva a hang
			globalSound = document.getElementById(audio);
			globalSound.cloneNode().play();
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


    // jatek zene be/ki
		function musicChange() {
			if (musicOff === true) // zene be
			{
				musicOff = false; // zene be
				window.localStorage.removeItem("MUSIC_OFF"); // mentes torlese
				$('#game_music .toggle_icon').attr('src','pic/toggle_on.png');

				loadMusic(); // Zene betoltese es inditasa
			}
			else // zene ki
			{
				musicOff = true; // zene ki
				window.localStorage.setItem("MUSIC_OFF", 1); // mentes
				$('#game_music .toggle_icon').attr('src','pic/toggle_off.png');

				unloadMusic(); // Zene torlese a memoriabol
			}
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


    // jatek hang be/ki
		function soundChange() {
			if (soundOff === true) // hang be
			{
				soundOff = false; // hang be
				window.localStorage.removeItem("SOUND_OFF"); // mentes torlese
				$('#game_sound .toggle_icon').attr('src','pic/toggle_on.png');

				loadAudio(1); // Hangok betoltese
			}
			else // hang ki
			{
				soundOff = true; // hang ki
				window.localStorage.setItem("SOUND_OFF", 1); // mentes
				$('#game_sound .toggle_icon').attr('src','pic/toggle_off.png');

				unloadAudio(); // Hangok torlese a memoriabol
			}
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


    // jatek rezges be/ki
		function vibrateChange() {
			if (vibrateOff === true) // rezges be
			{
				vibrateOff = false; // rezges be
				window.localStorage.removeItem("VIBRATE_OFF"); // mentes torlese
				$('#game_vibrate .toggle_icon').attr('src','pic/toggle_on.png');
				if (cordova_js) navigator.notification.vibrate(500); // rezgunk
			}
			else // rezges ki
			{
				vibrateOff = true; // rezges ki
				window.localStorage.setItem("VIBRATE_OFF", 1); // mentes
				$('#game_vibrate .toggle_icon').attr('src','pic/toggle_off.png');
			}
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


    // oldal csere
		function sideChange() {
			if (yourSide === 0) // Forditott felallas (fekete lent)
			{
				yourSide = 8; // felallas csere
				window.localStorage.setItem("KI_KEZDHET", yourSide); // mentes
				$('#player_1_side').animate({'left': '+='+105}, 300, false); // feher oldal csere
				$('#player_2_side').animate({'right': '+='+105}, 300, false); // fekete oldal csere
			}
			else // Alap felallas (feher lent)
			{
				yourSide = 0; // felallas csere
				window.localStorage.setItem("KI_KEZDHET", yourSide); // mentes
				$('#player_1_side').animate({'left': '-='+105}, 300, false); // feher oldal vissza
				$('#player_2_side').animate({'right': '-='+105}, 300, false); // fekete oldal vissza
			}
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


    // koordinatak be/ki
		function koordChange() {
			if (koordinateOff == true) // jelzes be
			{
				koordinateOff = false; // jelzes be
				window.localStorage.removeItem("KOORDINATE_OFF"); // mentes torlese
				$('#game_koordinate .toggle_icon').attr('src','pic/toggle_on.png');

				quietBoardUpdate(); // Tabla frissites
			}
			else // jelzes ki
			{
				koordinateOff = true; // jelzes ki
				window.localStorage.setItem("KOORDINATE_OFF", 1); // mentes
				$('#game_koordinate .toggle_icon').attr('src','pic/toggle_off.png');

				quietBoardUpdate(); // Tabla frissites
			}
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


    // babuk elforgatasa (2 jatekos modban)
		function rotatePieceChange() {
			if (rotatePiece == false) // elforgatas be
			{
				rotatePiece = true; // elforgatas be
				window.localStorage.removeItem("BABUFORGATAS_OFF"); // mentes torlese
				$('#game_rotatepiece .toggle_icon').attr('src','pic/toggle_on.png');
			}
			else // elforgatas ki
			{
				rotatePiece = false; // elforgatas ki
				window.localStorage.setItem("BABUFORGATAS_OFF", 1); // mentes
				$('#game_rotatepiece .toggle_icon').attr('src','pic/toggle_off.png');
			}
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


    // en passant lepes jelzo
		function EPAlertChange(id) {
			if (EPAlertOff == true) // jelzes be
			{
				EPAlertOff = false; // jelzes be
				window.localStorage.removeItem("EP_ALERT_OFF"); // mentes torlese
				$('#game_epalert .toggle_icon').attr('src','pic/toggle_on.png');
			}
			else // jelzes ki
			{
				EPAlertOff = true; // jelzes ki
				window.localStorage.setItem("EP_ALERT_OFF", 1); // mentes
				$('#game_epalert .toggle_icon').attr('src','pic/toggle_off.png');
				if (!id) {
					global_info('<div style="text-decoration:underline;padding:5px 0px">'+LANGUAGE.ep_alert_off_title+'</div>'
					+'<div style="font-size:15px;padding-bottom:5px"><table widht="100%"><tr><td valign="top"><img src="pic/en_passant.png" width=80></td>'
					+'<td valign="top">'+LANGUAGE.ep_alert_off_msg_1+''+LANGUAGE.ep_alert_off_msg_2+'</td></tr></table></div>'
					+'<a class="ok_gomb" href="javascript:void(0)" alt="global_info_close">'+LANGUAGE.okay_button+'</a>');
				}
			}
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


    // tabla szin
		function boardColor(option) {

			var tabla_szin = [ 'default_image', 'green', 'blue', 'dark_blue', 'gray' ]; // Tabla szinek
			var color_num = parseInt($('#board_color_div').attr('data-board_color')); // aktualis szin

			if (option == '-') { // Negativ iranyba lapozunk
				if (color_num > 0) {
					color_num--;
				} else {
					color_num = tabla_szin.length-1;
				}
			} else if (option == '+') { // Pozitiv iranyba lapozunk
				if (color_num < tabla_szin.length-1) {
					color_num++;
				} else {
					color_num = 0;
				}
			} else { // Szin beallitasa betolteskor
				for (var index = 0; index < tabla_szin.length; index++) {
					if (tabla_szin[index] == option) {
						color_num = index; // Elmentett szin szama
					}
				}
			}

			if (tabla_szin[color_num] != undefined) { // Ervenyes szin
				var color = tabla_szin[color_num];
			} else {
				var color = 'default_image'; // Ha ervenytelen a szin
			}

			if (option == '-' || option == '+') {
				window.localStorage.setItem("TABLA_SZIN", color); // mentes
			}

			BOARD_COLOR = color; // Valasztott szin

			// Class-ok torlese a beallitasnal
			for (var index = 0; index < tabla_szin.length; index++) {
				$('.board_example_dark').removeClass('b_color_'+index);
			}

			// Class hozzadasa
			$('.board_example_dark').addClass('b_color_'+color_num);

			// Szam attvetele
			$('#board_color_div').attr('data-board_color', color_num);

		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


    // babu kinezet
		function pieceStyle(option) {

			var piece_list = [ '', '_BABU_2', '_BABU_3' ]; // Valaszthato babuk
			var piece_num = parseInt($('#piece_style_div').attr('data-piece_style')); // aktualis babu

			if (option == '-') { // Negativ iranyba lapozunk
				if (piece_num > 0) {
					piece_num--;
				} else {
					piece_num = piece_list.length-1;
				}
			} else if (option == '+') { // Pozitiv iranyba lapozunk
				if (piece_num < piece_list.length-1) {
					piece_num++;
				} else {
					piece_num = 0;
				}
			} else { // Babu beallitasa betolteskor
				for (var index = 0; index < piece_list.length; index++) {
					if (piece_list[index] == option) {
						piece_num = index; // Elmentett babu szama
					}
				}
			}

			if (piece_list[piece_num] != undefined) { // Ervenyes babu
				var style = piece_list[piece_num];
			} else {
				var style = ''; // Ha ervenytelen a babu
			}

			if (option == '-' || option == '+') {
				window.localStorage.setItem("BABU_STYLE", style); // mentes
			}

			BABU_STYLE = style; // Valasztott babu

			// Minta valtas
			$('#piece_example img').eq(0).attr('src', 'pic/babuk_'+(piece_num+1)+'/bKnight.png');
			$('#piece_example img').eq(1).attr('src', 'pic/babuk_'+(piece_num+1)+'/wPawn.png');

			// Szam attvetele
			$('#piece_style_div').attr('data-piece_style', piece_num);

		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


    // nyelvek le/felnyitasa
		function translateMenu() {
			if ( $('#game_languages').is(":hidden") ) {
				$('#game_languages').slideDown('fast', function() { }); // lenyitas
			} else {
				$('#game_languages').slideUp('fast', function() { }); // becsukas
			}
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


    // szabalyok le/felnyitasa
		function rulesChange(id) {

			if (!id || id == undefined || isNaN(id)) { // ervenytelen id
				return false;
			} else {
				id = $('#rules_content_'+id); // jquery object

				if ( id.is(":hidden") ) {
					$('.rules_content_door').slideUp('fast'); // osszes becsukas
					id.slideDown('fast', function() { // lenyitas, majd scrollozas
						$('#rules_content').animate({ scrollTop: 0 }, "slow");
					});
				} else {
					id.slideUp('fast', function() { }); // becsukas
				}
			}
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


    // tabla frissites, hang nelkul
		function quietBoardUpdate() {
			var sound = soundOff; // Ujrarazolas (lepes)hang nelkul
			var last_move = [ -1, -1 ]; // Utolso lepes koordinatak
			$('#game_table .last_step').each(function(i) { // Elozmeny
				last_move[i] = $(this).attr('data-square');
			});
			var Move = BIT_MOVE(last_move[0], last_move[1], 0, 0, 0);
			Move = Move < NOMOVE ? NOMOVE : Move; // Hack!
			if (!sound) soundOff = true; // hang ki
			drawBoard(CHESS_BOARD, Move); // Tabla rajzolasa
			if (!sound) soundOff = false; // hang be
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


    // jatek menu kezelese
		function gameMenu(id) {

			if (menuAnim === true) { // Menu animacio fut
				return false;
			} else if (id != 'open') {
				menuAnim = true; // BUGFIX: animacio be
			}

		// menupontok
			if (id == 'open') { // JATEKMODOK FUL LENYITASA/BECSUKASA A FOMENUBEN

				if ( $('#game_mode').is(":hidden") ) {
					$('#game_mode').slideDown('fast', function() { }); // lenyitas
				} else {
					$('#game_mode').slideUp('fast', function() { }); // becsukas
				}

				return false; // kilepunk

			} else if (id == 'about') { // INFORMACIOK MENU

				playAudio('menu_slash'); // menu lapozas hang

				$('#content').css({'width': anim_diff_3}); // content 3 ablak
				$('#game_between').children().css({'display':'none'}); // menuk ki
				$('#game_between').css({'display':'block'}); // beallitas menu be
				$('#game_about').css({'display':'block'}); // informaciok menu be

				$('#content').animate({'margin-left': '-'+anim_diff_1}, 300, function() { // koztes menu megnyitasa
					menuAnim = false; // BUGFIX: animacio kesz
					$('#logo').removeClass('menu_logo'); // logo oldalra kerul
					$('#menu_button').css({'display':'block'}); // menu gomb megjelenitese
				});

				return true; // kilepunk

			} else if (id == 'rules') { // SZABALYOK MENU

				playAudio('menu_slash'); // menu lapozas hang

				$('#content').css({'width': anim_diff_3}); // content 3 ablak
				$('#game_between').children().css({'display':'none'}); // menuk ki
				$('#game_between').css({'display':'block'}); // beallitas menu be
				$('#game_rules').css({'display':'block'}); // szabalyok menu be

				$('#content').animate({'margin-left': '-'+anim_diff_1}, 300, function() { // koztes menu megnyitasa
					menuAnim = false; // BUGFIX: animacio kesz
					$('#logo').removeClass('menu_logo'); // logo oldalra kerul
					$('#menu_button').css({'display':'block'}); // menu gomb megjelenitese
				});

				return true; // kilepunk

			} else if (id == 'options') { // ALAP BEALLITASOK MENU

				playAudio('menu_slash'); // menu lapozas hang

				$('#content').css({'width': anim_diff_3}); // content 3 ablak
				$('#game_between').children().css({'display':'none'}); // menuk ki
				$('#game_between').css({'display':'block'}); // beallitas menu be
				$('#game_options').css({'display':'block'}); // alapbeallitasok be

				$('#content').animate({'margin-left': '-'+anim_diff_1}, 300, function() { // koztes menu megnyitasa
					menuAnim = false; // BUGFIX: animacio kesz
					$('#logo').removeClass('menu_logo'); // logo oldalra kerul
					$('#menu_button').css({'display':'block'}); // menu gomb megjelenitese
				});

				return true; // kilepunk

			} else if (id == 'statistics') { // EREDMENYEK MENU

				playAudio('menu_slash'); // menu lapozas hang

				var stat = gameStat(); // Statisztika betoltese
				$('#stat_content').html(stat); // Statisztika html-be
				$('#content').css({'width': anim_diff_3}); // content 3 ablak
				$('#game_between').children().css({'display':'none'}); // menuk ki
				$('#game_between').css({'display':'block'}); // beallitas menu be
				$('#game_stat').css({'display':'block'}); // alapbeallitasok be

				$('#content').animate({'margin-left': '-'+anim_diff_1}, 300, function() { // koztes menu megnyitasa
					menuAnim = false; // BUGFIX: animacio kesz
					$('#logo').removeClass('menu_logo'); // logo oldalra kerul
					$('#menu_button').css({'display':'block'}); // menu gomb megjelenitese
				});

				return true; // kilepunk

			} else if (id == 'single') { // GEP ELLEN BEALLITAS MENU

				var oldGameMode = gameMode; // eredeti jatekmod mentese
				gameMode = 1; // gep ellen jatszunk

				if (!Game_Restart(3)) { // ha nem kezdtunk uj merkozest
					gameMode = oldGameMode; // eredeti jatekmodot vissza
					menuAnim = false; // BUGFIX: animacio kesz
					return false;
				}

				playAudio('menu_slash'); // menu lapozas hang

				$('#game_help').removeClass('hidden'); // segiseg gomb be
				$('#content').css({'width': anim_diff_3}); // content 3 ablak
				$('#game_power').css({'display':'block'}); // erosseg allitas be
				$('#game_between').children().css({'display':'none'}); // menuk ki
				$('#game_between').css({'display':'block'}); // beallitas menu be
				$('#new_game_menu').css({'display':'block'}); // jatek beallitas be
				$('#game_rotatepiece').css({'display':'none'}); // forgatas opcio ki
				$('#side_name_1').html(LANGUAGE.single_side_name_1).removeClass('small'); // 1.jatekos
				$('#side_name_2').html(LANGUAGE.single_side_name_2).removeClass('small'); // 2.jatekos

				$('#content').animate({'margin-left': '-'+anim_diff_1}, 300, function() { // koztes menu megnyitasa
					menuAnim = false; // BUGFIX: animacio kesz
					$('#logo').removeClass('menu_logo'); // logo oldalra kerul
					$('#welcome').css({'display':'block'}); // udvozlo szoveg be
					$('#game_resume').css({'display':'none'}); // vissza a jatekba ki
					$('#menu_button').css({'display':'block'}); // menu gomb megjelenitese
				});

				return true; // kilepunk

			} else if (id == 'multi') { // 2 JATEKOS MOD BEALLITAS MENU

				var oldGameMode = gameMode; // eredeti jatekmod mentese
				gameMode = 2; // 1v1 modban jatszunk

				if (!Game_Restart(3)) { // ha nem kezdtunk uj merkozest
					gameMode = oldGameMode; // eredeti jatekmodot vissza
					menuAnim = false; // BUGFIX: animacio kesz
					return false;
				}

				playAudio('menu_slash'); // menu lapozas hang

				$('#game_help').addClass('hidden'); // segiseg gomb ki
				$('#content').css({'width': anim_diff_3}); // content 3 ablak
				$('#game_power').css({'display':'none'}); // erosseg allitas ki
				$('#game_between').children().css({'display':'none'}); // menuk ki
				$('#game_between').css({'display':'block'}); // beallitas menu be
				$('#new_game_menu').css({'display':'block'}); // jatek beallitas be
				$('#game_rotatepiece').css({'display':'block'}); // forgatas opcio be
				$('#side_name_1').html(LANGUAGE.multi_side_name_1).addClass('small'); // 1.jatekos
				$('#side_name_2').html(LANGUAGE.multi_side_name_2).addClass('small'); // 2.jatekos

				$('#content').animate({'margin-left': '-'+anim_diff_1}, 300, function() { // koztes menu megnyitasa
					menuAnim = false; // BUGFIX: animacio kesz
					$('#logo').removeClass('menu_logo'); // logo oldalra kerul
					$('#welcome').css({'display':'block'}); // udvozlo szoveg be
					$('#game_resume').css({'display':'none'}); // vissza a jatekba ki
					$('#menu_button').css({'display':'block'}); // menu gomb megjelenitese
				});

				return true; // kilepunk

			} else if (id == 'play') { // BELEPUNK AZ UJ JATEKBA

				if (Game_Restart(4)) // elinditjuk az uj jatekot
				{
					playAudio('menu_slash'); // menu lapozas hang

					$('#content').animate({'margin-left': '-'+anim_diff_2}, 300, function() { // jatekoldal megnyitasa

						// EGYIDOBEN FUTNAK LE >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
						$('#content').animate({'margin-left': '-'+anim_diff_1, 'width': anim_diff_2}, 0, false); // content 2 ablak

						$('#game_between').animate({'width': '0px'}, 0, false, function() { // koztes menu >> 0px
							menuAnim = false; // BUGFIX: animacio kesz
							$('#welcome').css({'display':'none'}); // udvozles eltunik
							$('#game_resume').css({'display':'block'}); // folytatas gomb be
							$('#game_between').css({'display':'none', 'width': anim_diff_1}); // koztes menu ki + szelesseg novelese
						});
						// EGYIDOBEN FUTNAK LE >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

					});
				} else {
					alert('Hiba! Indítsd újra az alkalmazást!')
				}

				return true; // kilepunk

			} else if (id == 'resume') { // MEGKEZDETT JATEK FOLYTATASA

				playAudio('menu_slash'); // menu lapozas hang

				$('#content').animate({'margin-left': '-'+anim_diff_1}, 300, function() { // jatekoldal megnyitasa
					menuAnim = false; // BUGFIX: animacio kesz
					$('#logo').removeClass('menu_logo'); // logo oldalra kerul
					$('#menu_button').css({'display':'block'}); // menu gomb megjelenitese
				});

				return true; // kilepunk

			} else if (id == 'menu') { // FOMENUBE LEPES

				playAudio('menu_slash'); // menu lapozas hang

				$('#logo').addClass('menu_logo'); // fomenuben kozepen van a logo
				$('#game_mode').css({'display':'none'}); // jatekmodok menu ful ki
				$('#menu_button').css({'display':'none'}); // menugomb eltuntetese
				$('#content').animate({'margin-left': '0px'}, 300, function() { // fomenu megnyitasa
					menuAnim = false; // BUGFIX: animacio kesz
					$('#game_between').css({'display':'none'}); // koztes menu ki
					$('#game_languages').css({'display':'none'}); // nyelv menu bezaras
					$('.rules_content_door').css({'display':'none'}); // szabaly ablakok ki
				});

				return true; // kilepunk
			}
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


    // jatek statisztika
		function gameStat() {
			var result = '';
			// var best_stat = window.localStorage.getItem("best_stat");
			var veresegek = JSON.parse(window.localStorage.getItem("vereseg_stat"));
			var gyozelemek = JSON.parse(window.localStorage.getItem("gyozelem_stat"));
			var dontetlenek = JSON.parse(window.localStorage.getItem("dontetlen_stat"));

			result += '<table width="100%"><tr>';
			result += '<td><u>'+LANGUAGE.result_stat_level+'</u></td>';
			result += '<td><u>'+LANGUAGE.result_stat_winner+'</u></td>';
			result += '<td><u>'+LANGUAGE.result_stat_lost+'</u></td>';
			result += '<td><u>'+LANGUAGE.result_stat_draw+'</u></td>';
			result += '<td><u>'+LANGUAGE.result_stat_rate+'</u></td></tr>';

			for (var index = (Object.keys(gep_szint).length - 1); index >= 0; index--)
			{
				var vereseg = (veresegek ? (veresegek[index] != undefined ? veresegek[index] : 0) : 0);
				var gyozelem = (gyozelemek ? (gyozelemek[index] != undefined ? gyozelemek[index] : 0) : 0);
				var dontetlen = (dontetlenek ? (dontetlenek[index] != undefined ? dontetlenek[index] : 0) : 0);
				var szazalek = (gyozelem / (vereseg+gyozelem+dontetlen));
				if (isNaN(szazalek)) szazalek = 0;

				result += '<tr><td style="border:1px solid black;background-color:#f6af5f;text-shadow:none;">'+ 
							(index + 1)
						+'</td><td style="border:1px solid black;background-color:#92c9a4;text-shadow:none;">'+
							gyozelem
						+'</td><td style="border:1px solid black;background-color:#dd7793;text-shadow:none;">'+
							vereseg
						+'</td><td style="border:1px solid black;background-color:#b7b6b1;text-shadow:none;">'+
							dontetlen
						+'</td><td style="border:1px solid black;background-color:#a5a39e;text-shadow:none;">'+
							szazalek.toFixed(2)
						+'</td></tr>';
			}

			result += '</table>';

			return result;
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


    // statisztika torles megerositese
		function gameStatClear() {
			if (cordova_js) // betoltodott a cordova.js
			{
				navigator.notification.confirm(
					LANGUAGE.delete_confirm, // Uzenet
					gameStatDel, // Funkcio
					LANGUAGE.confirm_title, // Cim
					[LANGUAGE.yes_button, LANGUAGE.no_button] // Gomb
				);
			} else {
				gameStatDel('1'); // Bongeszoben
			}
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


    // statisztika torles megerositese
		function gameStatDel(gomb) {
			if (gomb == 1) {
				//window.localStorage.clear(); // mindent torol
				window.localStorage.removeItem("best_stat"); // torles
				window.localStorage.removeItem("vereseg_stat"); // torles
				window.localStorage.removeItem("gyozelem_stat"); // torles
				window.localStorage.removeItem("dontetlen_stat"); // torles

				if (cordova_js) // betoltodott a cordova.js
				{
					navigator.notification.alert(
						LANGUAGE.result_delete_ok, // Uzenet
						false, // Funkcio
						LANGUAGE.confirm_succes, // Cim
						LANGUAGE.okay_button // Gomb
					);
				} else { // Bongeszoben
					alert(LANGUAGE.result_delete_ok);
				}

			// Nullazott Statisztika kiirasa
				var stat = gameStat(); // Statisztika betoltese
				$('#stat_content').html(stat); // Statisztika html-be
			}
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// Uj jatek
		function Game_Restart(id) {

			if (id == 2) return false; // Bezaras gombra nyomtak a felugro ablakon

			var worker_kereses = false; // volt-e worker kereses folyamatban

			if (maxSearchTime !== 0) { // ha epp keres a gep
				if (onMoveLoop === true) { // Lepes folyamatban
					return false;
				}
				if (InitBackgroundEngine()) { // Worker leallitasa
					WorkerStop();
					maxSearchTime = 0;
					worker_kereses = true;
					ChessEngineRestart(); // Sakk motor ujrainditas
				} else { // Worker nelkul meg kell varnunk a kereses veget
					return false;
				}
			}

			if (moveCount > 0 && JATEK_FOLYAMATBAN === true) { // ha folyamatban van mar egy jatek

				if (cordova_js) // betoltodott a cordova.js
				{
					var game_mode = gameMode; // Menubol hivas BUGFIX
					navigator.notification.confirm(
						LANGUAGE.new_game_confirm, // Uzenet
						function(gomb) { // Funkcio
							if (gomb == 1) {
								JATEK_FOLYAMATBAN = false; // Jatek vege
								moveCount = 0;
								if (id == 3) {
									return (game_mode == 1) ? gameMenu('single') : gameMenu('multi'); // 1.Jatek mod valtas, 2.Ujrainditas
								} else {
									return Game_Restart(); // Azonnali uj jatek inditasa (id == 4)
								}
							} else {
								if (worker_kereses && helpLoop === false) { // ha keresett a gep akkor ujra inditjuk

									setTimeout(function() { // ido eltolas a "gameMode" allapot miatt
										if (currentPlayer !== yourSide && gameMode === 1) { // Csak gep ellen
											FindMove(0);
										}
									}, 100);

								} else if (worker_kereses && helpLoop === true) { // ha segitsegkeres kozben nyomtunk nemet az uj jatekra

									setTimeout(function() { FindMove(1); }, 100); // ido eltolas a "gameMode" allapot miatt

								}
								return false;
							}
						},
						LANGUAGE.confirm_title, // Cim
						[LANGUAGE.yes_button, LANGUAGE.no_button] // Gomb
					);
					return false; // Minden esetben false erteket adunk vissza -> menubol hivas BUGFIX

				} else {

					var r = confirm(LANGUAGE.new_game_confirm);
					if (r == false) {
						if (worker_kereses && helpLoop === false) { // ha keresett a gep akkor ujra inditjuk

							setTimeout(function() { // ido eltolas a "gameMode" allapot miatt
								if (currentPlayer !== yourSide && gameMode === 1) { // Csak gep ellen
									FindMove(0);
								}
							}, 100);

						} else if (worker_kereses && helpLoop === true) { // ha segitsegkeres kozben nyomtunk nemet az uj jatekra

							setTimeout(function() { FindMove(1); }, 100); // ido eltolas a "gameMode" allapot miatt

						}
						return false;
					}
				}
			}

		// Uj jatek eseten toroljuk a mentest
			window.localStorage.removeItem("JATEK_MOD");
			window.localStorage.removeItem("MOVE_HISTORY");
			window.localStorage.removeItem("CASTLE_KEYS_HIGH");
			window.localStorage.removeItem("CASTLE_KEYS_LOW");
			window.localStorage.removeItem("PIECE_KEYS_HIGH");
			window.localStorage.removeItem("PIECE_KEYS_LOW");
			window.localStorage.removeItem("SIDE_KEY_HIGH");
			window.localStorage.removeItem("SIDE_KEY_LOW");
			window.localStorage.removeItem("FEN");

			if (id == 3) { // Uj jatek menubol ellenoriztunk
				JATEK_FOLYAMATBAN = false; // Jatek vege
				moveCount = 0; // Lepesszam nullazas
				return true;
			}

			onMoveLoop = false; // Lepes kesz
			moveCount = 0; // Lepesszam nullazas
			brd_fiftyMove = 0; // 50 lepes nullazas
			maxSearchTime = 0; // Kereses ido nullazas
			JATEK_FOLYAMATBAN = true; // Jatek folyamatban
			MOVE_HISTORY = new Array(); // Lepes elozmenyek torlese
			//yourSide = yourSide ? 0 : 8; // Oldalvaltas uj jateknal
			START_FEN = 'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR '+(yourSide ? 'b' : 'w')+' KQkq - 0 0';

			CHESS_BOARD = FENToBoard(); // Tabla feltoltese

			ChessEngineRestart(); // Sakk motor ujrainditas

			if (yourSide) { // forditott tablanal embert kell valtani a tablarajzolas elott
				currentPlayer ^= 8; // ezzel elkerulendo a dragable BUG
			}

			drawBoard(CHESS_BOARD, NOMOVE); // Tabla rajzolasa

			if (GameOver()) { // Nincs ervenyes lepes
				$('#game_info').html(LANGUAGE.game_over);
				JATEK_FOLYAMATBAN = false; // Jatek vege
				return true;
			}

			if (yourSide && gameMode === 1) { // Gep elso lepese Feher oldalon
				SearchStartInfo(); // ertesito update
				var time = id == 4 ? 400 : 100; // menubol : jatek
				setTimeout(function() { FindMove(0); }, time); // ido eltolas menubol 0,4s jatek 0,1s
			}

			return true;
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// getPieceName
		function getPieceName(pieceValue) {
			switch (pieceValue) {
				case WHITE_KING: return 'WHITE_KING';
				case WHITE_QUEEN: return 'WHITE_QUEEN';
				case WHITE_ROOK: return 'WHITE_ROOK';
				case WHITE_BISHOP: return 'WHITE_BISHOP';
				case WHITE_KNIGHT: return 'WHITE_KNIGHT';
				case WHITE_PAWN: return 'WHITE_PAWN';
					
				case BLACK_KING: return 'BLACK_KING';
				case BLACK_QUEEN: return 'BLACK_QUEEN';
				case BLACK_ROOK: return 'BLACK_ROOK';
				case BLACK_BISHOP: return 'BLACK_BISHOP';
				case BLACK_KNIGHT: return 'BLACK_KNIGHT';
				case BLACK_PAWN: return 'BLACK_PAWN';
					
				default: return 'EMPTY';
			}
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// Tabla kirajzolasa
		function drawBoard(BOARD, Move) {

			var piece_num = 0;
			var moveFromClick = -1;
			var last_to = TOSQ(Move);
			var last_from = FROMSQ(Move);
			var whichPlayer = yourSide ? 0 : 8;
			var incr = whichPlayer ? 1 : -1;
			var start = whichPlayer ? 0 : 127;
			var end = whichPlayer ? 128 : -1;
			var rowStart = whichPlayer ? 0 : 15;
			var rowEnd = whichPlayer ? 15 : 0;
			var rotate = (gameMode == 2 && rotatePiece && (yourSide ? moveCount % 2 == 0 : moveCount % 2 != 0));

		//>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Kiiras nullazasa
			if (gameMode === 1) { // gep ellen

				$('#game_info').html(LANGUAGE.you_turn);

			} else { // 2 jatekos jatszik
				if (moveCount % 2 === 0) {
					$('#game_info').html(LANGUAGE.white_turn);
				} else {
					$('#game_info').html(LANGUAGE.black_turn);
				}
			}

		// Szamozas kezdo ertek
			if (whichPlayer) {
				var last_row = 1;
				var board_line = 8;
			} else {
				var last_row = 8;
				var board_line = 1;
			}

		//>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			var str = '<table border="0" cellpadding="0px" cellspacing="0px">'; // Tabla keret

		// Tabla felepitese
			for (var index = start; index !== end; index+= incr) 
			{
			// Szamozas, betuzes
				var board_cell = index % 16;
				var board_strs = "abcdefgh";
				var board_str = board_strs.substr(board_cell, 1);
				var color = (index & 0x1) ^ ((index >> 4) & 0x1);

			// Babuk szamolasa
				if (BOARD[index]) piece_num++;

			// Sor eleje
				if (index % 16 == rowStart) {
					str += '<tr class="row">';
				}

			// Mezok
				if (!(index & 0x88)) {
					str += '<td class="column_td">';

					if (!koordinateOff && (whichPlayer ? (index % 16 == rowStart) : (index % 16 == 7))) { // Sor Koordinata
						str += '<div class="numbers '+(color ? 'light '+BOARD_COLOR : 'dark '+BOARD_COLOR)+'">'+board_line+'</div>';
					}

					str += '<div class="column '+(color ? ('dark '+BOARD_COLOR) : ('light '+BOARD_COLOR))+
							'"data-square="'+index+'" alt="'+board_str + Math.round(board_line) + '">'+
								'<div class="drag_and_drop"></div>'+
								'<div class="'+getPieceName(BOARD[index])+''+(BOARD[index] ? BABU_STYLE : '')+' '+(rotate ? 'rotate' : '')+'"></div>'+
							'</div>';

					if (!koordinateOff && board_line == last_row) { // Oszlop Koordinata
						str += '<div class="letters '+(color ? 'light '+BOARD_COLOR : 'dark '+BOARD_COLOR)+'">'+board_str+'</div>';
					}

					str += '</td>';
				}

			// Sor vege
				if (index % 16 == rowEnd) {
					str += '</tr>';

					if (whichPlayer) { // Szamozas
						board_line--;
					} else {
						board_line++;
					}
				}
			}

			str += '</table>'; // Tabla vege

		// Tabla html-be
			$('#game_table').html(str);

		//>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Volt lepes
			if (Move != NOMOVE)
			{
			// Utolso lepes jelzese
				$('div[data-square="'+last_to+'"]').addClass('last_step'); // hova leptunk
				$('div[data-square="'+last_from+'"]').addClass('last_step'); // honnan leptunk

			// Dontetlen
				if ((piece_num < 3) // 2 kiraly
				|| (brd_fiftyMove > 100) // 50 lepesszabaly
				|| (ThreeFoldRep() >= 2) // 3 lepesismetles
				|| (brd_Material[WHITE] == PieceValue[KING] && brd_Material[BLACK] == (PieceValue[KING] + PieceValue[KNIGHT])) // WKing vs BKing + B(N|B)
				|| (brd_Material[BLACK] == PieceValue[KING] && brd_Material[WHITE] == (PieceValue[KING] + PieceValue[KNIGHT]))) // BKing vs WKing + W(N|B)
				{
				// hang
					playAudio('game_egal');

				// dontetlen szoveg
					if (brd_fiftyMove > 100) {
						var draw_msg = LANGUAGE.game_draw_msg_3; // 50 lepesszabaly
					} else if (ThreeFoldRep() >= 2) {
						var draw_msg = LANGUAGE.game_draw_msg_2; // 3 lepesismetles
					} else {
						var draw_msg = LANGUAGE.game_draw_msg_1; // Nincs eleg babu
					}

				// info kiiras
					$('#game_info').html(draw_msg);

				// statisztika frissitese gep ellen
					if (gameMode === 1 && JATEK_FOLYAMATBAN)
					{
						var statArray = new Array(Object.keys(gep_szint).length); // Koztes tarolo
						var statNum = JSON.parse(window.localStorage.getItem("dontetlen_stat")); // Mentet adatok

						for (var index = 0; index < statArray.length; index++) // Koztes tarolo feloltese
						{
							statArray[index] = (statNum ? (statNum[index] != undefined ? statNum[index] : 0) : 0);
						}
						if (gep_szint[ALPHA_BETA_MAX_IDO] != undefined) // Ha ervenyes a szint
						{
							statArray[ gep_szint[ALPHA_BETA_MAX_IDO]-1 ]++; // Noveljuk a statisztikat
							window.localStorage.setItem("dontetlen_stat", JSON.stringify(statArray)); // Statisztika mentese
						}
					}

				// betoltodott a cordova.js
					if (cordova_js && JATEK_FOLYAMATBAN)
					{
					// uzenet
						navigator.notification.confirm(
							draw_msg, // Uzenet
							Game_Restart, // Funkcio
							LANGUAGE.result_stat_draw, // Cim
							[LANGUAGE.new_game, LANGUAGE.close] // Gomb
						);
					}

					JATEK_FOLYAMATBAN = false; // Jatek vege

					if (InitBackgroundEngine()) WorkerStop(); // Worker leallitasa

					return false;
				}

		//>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			// Sakk van?
				if (isCheck(currentPlayer))
				{
					var SAKK_VAN = true;

					if (gameMode === 1) { // gep ellen

						$('#game_info').html(LANGUAGE.you_turn_check); // Sakk! Te lepsz!

					} else { // 2 jatekos jatszik

						if (moveCount % 2 === 0) {
							$('#game_info').html(LANGUAGE.white_turn_check); // Sakk! Feher lep!
						} else {
							$('#game_info').html(LANGUAGE.black_turn_check); // Sakk! Fekete lep!
						}
					}

					$('div[data-square="'+brd_pieceList[(currentPlayer | KING) << 4]+'"]').addClass('king_sakk');
				}
				else
				{
					var SAKK_VAN = false;
				}

		//>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			// Jatek vege
				if (GameOver())
				{
					if (SAKK_VAN) // SAKK-MATT
					{
						if ((currentPlayer != yourSide) || (gameMode === 2)) // GYOZELEM
						{
							if (gameMode === 1) // gep ellen
							{
							// hang
								playAudio('game_winner');

							// kiiras
								$('#game_info').html(LANGUAGE.mate_you_win); // Te nyertel :)

							// statisztika frissitese
								if (JATEK_FOLYAMATBAN)
								{
									var statArray = new Array(Object.keys(gep_szint).length); // Koztes tarolo
									var statNum = JSON.parse(window.localStorage.getItem("gyozelem_stat")); // Mentet adatok

									for (var index = 0; index < statArray.length; index++) // Koztes tarolo feloltese
									{
										statArray[index] = (statNum ? (statNum[index] != undefined ? statNum[index] : 0) : 0);
									}
									if (gep_szint[ALPHA_BETA_MAX_IDO] != undefined) // Ha ervenyes a szint
									{
										statArray[ gep_szint[ALPHA_BETA_MAX_IDO]-1 ]++; // Noveljuk a statisztikat
										window.localStorage.setItem("gyozelem_stat", JSON.stringify(statArray)); // Statisztika mentese
									}

								// legerosebb legyozott!
									var max_ido = ALPHA_BETA_MAX_IDO;
									var best = window.localStorage.getItem("best_stat");
									window.localStorage.setItem("best_stat", (best ? (parseInt(best) < max_ido ? max_ido : best) : max_ido));
								}

							// betoltodott a cordova.js
								if (cordova_js && JATEK_FOLYAMATBAN)
								{
								// uzenet
									navigator.notification.confirm(
										LANGUAGE.mate_you_win, // Uzenet
										Game_Restart, // Funkcio
										LANGUAGE.check_mate, // Cim
										[LANGUAGE.new_game, LANGUAGE.close] // Gomb
									);
								}
							}
							else // 2 jatekos jatszik
							{
							// hang
								playAudio('game_winner');

							// kiiras
								if (moveCount % 2 === 0) {
									var win_msg = LANGUAGE.mate_black_win;
									$('#game_info').html(win_msg); // Fekete nyert
								} else {
									var win_msg = LANGUAGE.mate_white_win;
									$('#game_info').html(win_msg); // Feher nyert
								}

							// betoltodott a cordova.js
								if (cordova_js && JATEK_FOLYAMATBAN)
								{
								// uzenet
									navigator.notification.confirm(
										win_msg, // Uzenet
										Game_Restart, // Funkcio
										LANGUAGE.check_mate, // Cim
										[LANGUAGE.new_game, LANGUAGE.close] // Gomb
									);
								}
							}
						}
						else // VERESEGET CSAK GEP ELLEN IRJUK KI
						{
						// hang
							playAudio('game_looser');

						// kiiras
							$('#game_info').html(LANGUAGE.mate_you_lost); // Te vesztettel : (

 						// statisztika frissitese
							if (JATEK_FOLYAMATBAN)
							{
								var statArray = new Array(Object.keys(gep_szint).length); // Koztes tarolo
								var statNum = JSON.parse(window.localStorage.getItem("vereseg_stat")); // Mentet adatok

								for (var index = 0; index < statArray.length; index++) // Koztes tarolo feloltese
								{
									statArray[index] = (statNum ? (statNum[index] != undefined ? statNum[index] : 0) : 0);
								}
								if (gep_szint[ALPHA_BETA_MAX_IDO] != undefined) // Ha ervenyes a szint
								{
									statArray[ gep_szint[ALPHA_BETA_MAX_IDO]-1 ]++; // Noveljuk a statisztikat
									window.localStorage.setItem("vereseg_stat", JSON.stringify(statArray)); // Statisztika mentese
								}
							}

						// betoltodott a cordova.js
							if (cordova_js && JATEK_FOLYAMATBAN)
							{
							// uzenet
								navigator.notification.confirm(
									LANGUAGE.mate_you_lost, // Uzenet
									Game_Restart, // Funkcio
									LANGUAGE.check_mate, // Cim
									[LANGUAGE.new_game, LANGUAGE.close] // Gomb
								);
							}
						}
					}
					else // DONTETLEN
					{
					// hang
						playAudio('game_egal');

					// kiiras
						$('#game_info').html(LANGUAGE.game_draw_msg_4); // Patt :/

					// statisztika frissitese gep ellen
						if (gameMode === 1 && JATEK_FOLYAMATBAN)
						{
							var statArray = new Array(Object.keys(gep_szint).length); // Koztes tarolo
							var statNum = JSON.parse(window.localStorage.getItem("dontetlen_stat")); // Mentet adatok

							for (var index = 0; index < statArray.length; index++) // Koztes tarolo feloltese
							{
								statArray[index] = (statNum ? (statNum[index] != undefined ? statNum[index] : 0) : 0);
							}
							if (gep_szint[ALPHA_BETA_MAX_IDO] != undefined) // Ha ervenyes a szint
							{
								statArray[ gep_szint[ALPHA_BETA_MAX_IDO]-1 ]++; // Noveljuk a statisztikat
								window.localStorage.setItem("dontetlen_stat", JSON.stringify(statArray)); // Statisztika mentese
							}
						}

					// betoltodott a cordova.js
						if (cordova_js && JATEK_FOLYAMATBAN)
						{
						// uzenet
							navigator.notification.confirm(
								LANGUAGE.game_draw_msg_4, // Uzenet
								Game_Restart, // Funkcio
								LANGUAGE.result_stat_draw, // Cim
								[LANGUAGE.new_game, LANGUAGE.close] // Gomb
							);
						}
					}

					JATEK_FOLYAMATBAN = false; // Jatek vege

					if (InitBackgroundEngine()) WorkerStop(); // Worker leallitasa

					return false;
				}

		//>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			// Sakk Van!
				if (SAKK_VAN) {
					playAudio('sakk_sakk'); // hang

					if (cordova_js && vibrateOff === false) { // rezges
						navigator.notification.vibrate(500);
					}
				}

		//>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			// Lepes es utes hang
				if (!SAKK_VAN && (Move & CAPTURE_MASK)) { // utes volt es nem volt sakk

					playAudio('sakk_utes'); // hang

				} else if (!SAKK_VAN) { // sima lepes volt

					playAudio('sakk_lepes'); // hang

				}
			}

		//>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			if (currentPlayer === yourSide || gameMode === 2) { // Ha mi lephetunk gep ellen, vagy 2 jatekos modban jatszunk

			// Ellenfel elemeivel nem lephetunk
				$('.column div').filter(function() {
					return $(this).attr('class').indexOf(currentPlayer ? 'BLACK' : 'WHITE') !== -1;
				}).draggable({
					zIndex: 3,
					addClasses: false,
					revertDuration: 0,
					revert: function(event) {
						$(this).parent().removeClass('piece_drop piece_drag').find('div').attr('style', '');
						moveFromClick = $(this).parent().data('square'); // Ahonnan lepunk "kattintassal"
						return !event;
					}
				});

			// Babu mozgatasa "kattintassal"
				$('.column').on(clickEventType, function() {
					$('.column').removeClass('red-border from_class'); // Elozo kijelolesek torlese

					if ($(this).find('div').eq(1).attr('class').indexOf(currentPlayer ? 'BLACK' : 'WHITE') !== -1) { // Ahonnan lepunk
						$(this).addClass('from_class');
					}

					if (maxSearchTime === 0)
					{
						if (validateMove(moveFromClick, $(this).data('square'), currentPlayer)) { // Mar van ahonnan lepunk

							onMove(moveFromClick, $(this).data('square'), false, false, false);

						} else {
							moveFromClick = -1; // BUGFIX: Felejtse el ha masik mezore klikkeltunk

							for (var index = 0; index < 120; index++) {
								if (validateMove($(this).data('square'), index, currentPlayer)) { // Ervenyes mezok
									$('div[data-square="'+index+'"]').addClass('red-border');
									if (moveFromClick == -1) { // Ahonnan lepunk mentese
										moveFromClick = $(this).data('square');
									}
								}
							}
						}
					}
				});

			// Babu mozgatasa "huzassal"
				$('.column').mousedown(function(e) {

					DRAG_DIV = $(this); // Megerintett elem

					DRAG_DIV.droppable({ disabled: true }); // Android Hack! TODO: Ellenorizni kell!

					$('.column').removeClass('red-border from_class piece_drop piece_drag'); // Class Nullazas

					if (DRAG_DIV.find('div').eq(1).attr('class').indexOf(currentPlayer ? 'BLACK' : 'WHITE') !== -1) { // Ahonnan lepunk
						DRAG_DIV.addClass('from_class piece_drag').droppable({ // Babu felnagyitasa + Kor hozzaadasa
							disabled: false,
							addClasses: false,
							over: function(event, ui) {
								$(this).addClass('piece_drop');
							},
							out: function(event, ui) {
								$(this).removeClass('piece_drop');
							},
							drop: function(event, ui) {
								$(this).removeClass('piece_drop');
								$(ui.draggable).attr('style', '');
								moveFromClick = DRAG_DIV.data('square'); // Ahonnan lepunk "kattintassal"
							}
						});
						var PIECE_DIV = DRAG_DIV.find('div').eq(1); // Babu DIV
						var column_top = DRAG_DIV.offset().top; // Megerintett DIV pozicioja
						var relativeTop = (e.pageY - column_top); // Erintesi pozicio a DIV-en belul
						var img_size = parseInt(PIECE_DIV.css('background-size').split('px')[0]); // Babu merete
						var top_diff = parseInt(-img_size + relativeTop); // Babu "top" erteke
						PIECE_DIV.css('top', top_diff); // Babu eltolasa az erintes kezdesi pontjahoz
						top_diff = Math.abs(top_diff) + PIECE_DIV.position().top + 10; // Kor "top" erteke
						DRAG_DIV.addClass('piece_drop').find('div').eq(0).css({'margin-top': top_diff}); // Kiindulasi kor
					}

					if (maxSearchTime === 0)
					{
						for (var index = 0; index < 120; index++) {
							if (validateMove(DRAG_DIV.data('square'), index, currentPlayer)) { // Ervenyes mezok
								$('div[data-square="'+index+'"]').addClass('red-border').droppable({
									drop: onDrop,
									disabled: false,
									addClasses: false,
									over: function(event, ui) { $(this).addClass('piece_drop'); },
									out: function(event, ui) { $(this).removeClass('piece_drop'); }
								});
							}
						}
					}
				}).mouseup(function() { // Babu "elengedese"

					$('.column').filter(function(event) { // Android Bugfix!
						return !$(this).hasClass('piece_drop'); // Negalt!!
					}).droppable({
						disabled: true // Dobas kikapcsolasa
					});

					if (DRAG_DIV !== null) {
						DRAG_DIV.droppable({ // Ahonnan indultunk
							disabled: true // Dobas kikapcsolasa
						});
						DRAG_DIV = null; // Drag div nullazasa
					}

					$(this).removeClass('piece_drop piece_drag').find('div').attr('style', ''); // Drag-drop style torlese
				});
			}
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// babu elengedese lepeskor
		function onDrop(event, ui) {
			var to = $(this).data('square');
			var from = $(ui.draggable).parent().data('square');
			return onMove(from, to, false, false, true);
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// gyalogos atvaltoztatas
		function pawnPromotion(piece, from, to) {
			global_info_close(); // ablak bezaras
			return onMove(from, to, piece, false, false);
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// maga a lepes
		function onMove(from, to, PROMOTED_PIECE, COMPUTER, ON_DROP) {

			if (JATEK_FOLYAMATBAN && validateMove(from, to, currentPlayer))
			{
				if (helpLoop) // Segitseg kijelzese
				{
					helpLoop = false; // Segitseg nullazasa

					maxSearchTime = 0; // keresesi ido nullazasa

					$('div[data-square="'+from+'"], div[data-square="'+to+'"]').switchClass('', 'next_step', 0, function() {
						setTimeout(function() {
							$('div[data-square="'+from+'"], div[data-square="'+to+'"]').switchClass('next_step', '', 0, function() {
								$('#game_info').html(LANGUAGE.you_turn); // Te lepsz!
							});
						}, 1000);
					});

					return true;
				}

			// BUGFIX
				onMoveLoop = true; // Lepes folyamatban

			// gyalogos-csere eseten
				if ((CHESS_BOARD[from] & 0x07) === PAWN && !COMPUTER && !PROMOTED_PIECE && (to <= SQUARES.H8 || to >= SQUARES.A1))
				{
					var piece_num = parseInt($('#piece_style_div').attr('data-piece_style')) + 1; // Babu azonosito

					if (currentPlayer) // fekete oldal
					{
						global_info(LANGUAGE.pawn_promotion_msg
						+'<img src="pic/babuk_'+piece_num+'/bQueen.png" alt="'+BLACK_QUEEN+','+from+','+to+'" class="csere_babu">'
						+'<img src="pic/babuk_'+piece_num+'/bBishop.png" alt="'+BLACK_BISHOP+','+from+','+to+'" class="csere_babu">'
						+'<img src="pic/babuk_'+piece_num+'/bKnight.png" alt="'+BLACK_KNIGHT+','+from+','+to+'" class="csere_babu">'
						+'<img src="pic/babuk_'+piece_num+'/bRook.png" alt="'+BLACK_ROOK+','+from+','+to+'" class="csere_babu">');
						return false;

					} else { // feher oldal

						global_info(LANGUAGE.pawn_promotion_msg
						+'<img src="pic/babuk_'+piece_num+'/wQueen.png" alt="'+WHITE_QUEEN+','+from+','+to+'" class="csere_babu">'
						+'<img src="pic/babuk_'+piece_num+'/wBishop.png" alt="'+WHITE_BISHOP+','+from+','+to+'" class="csere_babu">'
						+'<img src="pic/babuk_'+piece_num+'/wKnight.png" alt="'+WHITE_KNIGHT+','+from+','+to+'" class="csere_babu">'
						+'<img src="pic/babuk_'+piece_num+'/wRook.png" alt="'+WHITE_ROOK+','+from+','+to+'" class="csere_babu">');
						return false;

					}
				}

			// Gyalog bevaltas ?
				PROMOTED_PIECE = PROMOTED_PIECE === false ? 0 : PROMOTED_PIECE;

			// Akival lepunk
				var fromPiece = CHESS_BOARD[from] & 0x07;

			// En Passant ?
				var EP_MOVE = 0;
				if (!CHESS_BOARD[to] && fromPiece === PAWN && EN_PASSANT != 0 && EN_PASSANT === to) {
					EP_MOVE = 1;
				}

			// Utes ?
				var CAPTURED = EP_MOVE; // Hack: En Passant is utes!
				if (CHESS_BOARD[to]) {
					CAPTURED = 1;
				}

			// Sancolas ?
				var CASTLING = 0;
				if (fromPiece === KING && Math.abs(from - to) === 2) {
					CASTLING = 1;
				}

			// Lepes generalas
				var MOVE = BIT_MOVE(from, to, CAPTURED, PROMOTED_PIECE, CASTLING);

			// lepes attadasa a gepnek
				makeMove(MOVE);

			// FEN a tablabol
				START_FEN = boardToFEN();

			// HA "onDrop"-AL LEPTUNK
				if (ON_DROP)
				{
				// Tabla rajzolasa
					drawBoard(CHESS_BOARD, MOVE);

				// keresesi ido nullazasa
					maxSearchTime = 0;

					if (JATEK_FOLYAMATBAN) { // Mehet tovabb a jatek

					// En Passant lepes
						if (EP_MOVE == 1 && EPAlertOff === false) {
							global_info('<div style="text-decoration:underline;padding:5px 0px">'+LANGUAGE.ep_move_title+'</div>'
							+'<div style="font-size:15px;padding-bottom:5px">'+LANGUAGE.ep_alert_off_msg_2+'</div>'
							+'<div style="font-size:15px;color:purple">'+LANGUAGE.ep_alert_off_info+'</div>'
							+'<a class="ok_gomb" href="javascript:void(0)" alt="global_info_close">'+LANGUAGE.okay_button+'</a>');
						}

						if (gameMode === 1) { // Gepi ellen

							if (currentPlayer != yourSide) { // Gepi lepes kovetkezik
								// ertesito update
									SearchStartInfo();

								// gepi lepes keresese
									setTimeout(function() { FindMove(0); }, ALPHA_BETA_MAX_IDO < 500 ? 500 : 100);
							}

						} else if (gameMode === 2) { // 2 jatekos jatszik

						}

					// Mentes az aktualis allapotrol, kilepes esetere
						window.localStorage.setItem("FEN", START_FEN);
						window.localStorage.setItem("JATEK_MOD", gameMode);
						window.localStorage.setItem("SIDE_KEY_LOW", SideKeyLow);
						window.localStorage.setItem("SIDE_KEY_HIGH", SideKeyHigh);
						window.localStorage.setItem("PIECE_KEYS_LOW", JSON.stringify(PieceKeysLow));
						window.localStorage.setItem("PIECE_KEYS_HIGH", JSON.stringify(PieceKeysHigh));
						window.localStorage.setItem("CASTLE_KEYS_LOW", JSON.stringify(CastleKeysLow));
						window.localStorage.setItem("CASTLE_KEYS_HIGH", JSON.stringify(CastleKeysHigh));
						window.localStorage.setItem("MOVE_HISTORY", JSON.stringify(MOVE_HISTORY));
					} else { // Vege a jateknak toroljuk a mentest
							window.localStorage.removeItem("JATEK_MOD");
							window.localStorage.removeItem("MOVE_HISTORY");
							window.localStorage.removeItem("CASTLE_KEYS_HIGH");
							window.localStorage.removeItem("CASTLE_KEYS_LOW");
							window.localStorage.removeItem("PIECE_KEYS_HIGH");
							window.localStorage.removeItem("PIECE_KEYS_LOW");
							window.localStorage.removeItem("SIDE_KEY_HIGH");
							window.localStorage.removeItem("SIDE_KEY_LOW");
							window.localStorage.removeItem("FEN");
					}

					onMoveLoop = false; // Lepes kesz

					return true; // kilepunk

				} else { // HA NEM "onDrop"-AL LEPTUNK

				// Elozo jelzes torlese
					$('.column').removeClass('last_step');

				// Babu mozgatasi mezok
					var TO_SQUARE = $('div[data-square="'+to+'"]');
					var FROM_SQUARE = $('div[data-square="'+from+'"]');
					var TO_PIECE = TO_SQUARE.find('div').eq(1);
					var FROM_PIECE = FROM_SQUARE.find('div').eq(1).zIndex(3); // z-index: 3

				// Utolso lepes jelzese
					TO_SQUARE.addClass('last_step');
					FROM_SQUARE.addClass('last_step');

				//Sancolas eseten Bastyamozgas parameterei
					if (CASTLING) {
						var rookTo = from + (from > to ? -1 : 1);
						var rookFrom = from + (from > to ? -4 : 3);
						var ROOK_TO = $('div[data-square="'+rookTo+'"]');
						var ROOK_FROM = $('div[data-square="'+rookFrom+'"]');
						var ROOK_PIECE = ROOK_FROM.find('div').eq(1);
						var rook_left = ROOK_TO.offset().left - ROOK_FROM.offset().left;
					}

				// Babumozgas parameterei
					var new_top = TO_SQUARE.offset().top - FROM_SQUARE.offset().top;
					var new_left = TO_SQUARE.offset().left - FROM_SQUARE.offset().left;

				// Animacio ideje
					var anim_time = 100; // ms
					var max_diff = Math.max(Math.abs(new_top), Math.abs(new_left));
					anim_time += Math.round(((max_diff / (anim_diff_1 / 8))-1) * (anim_diff_1 / 16));
					anim_time = Math.min(300, anim_time); // Maximum 300 ms

				// Ket jatekos, felso babu elforgatas BUGFIX
					if (gameMode == 2 && rotatePiece && currentPlayer == yourSide) { // makeMove utan
						var dir = -1;
						FROM_PIECE.velocity({ rotateZ: '180deg' }, 0, false, function() { });
						if (CASTLING) // Sancolas eseten
						ROOK_PIECE.velocity({ rotateZ: '180deg' }, 0, false, function() { });
					} else {
						var dir = 1;
					}

					setTimeout(function() { // KESLELTETES

					// BABUMOZGATAS ANIMACIO
						if (CASTLING) // Sancolas eseten egyidoben futnak le
						{
							ROOK_PIECE.velocity({ translateX: rook_left * dir }, anim_time, false, function() { });
						}
						FROM_PIECE.velocity({ translateX: new_left * dir, translateY: new_top * dir }, anim_time, false, function() {

							TO_PIECE.remove(); // Ahova lepunk eltuntetese

							setTimeout(function() { // KESLELTETES

							// Tabla rajzolasa
								drawBoard(CHESS_BOARD, MOVE);

							// keresesi ido nullazasa
								maxSearchTime = 0;

								if (JATEK_FOLYAMATBAN) { // Mehet tovabb a jatek

								// En Passant lepes
									if (EP_MOVE == 1 && EPAlertOff === false) {
										global_info('<div style="text-decoration:underline;padding:5px 0px">'+LANGUAGE.ep_move_title+'</div>'
										+'<div style="font-size:15px;padding-bottom:5px">'+LANGUAGE.ep_alert_off_msg_2+'</div>'
										+'<div style="font-size:15px;color:purple">'+LANGUAGE.ep_alert_off_info+'</div>'
										+'<a class="ok_gomb" href="javascript:void(0)" alt="global_info_close">'+LANGUAGE.okay_button+'</a>');
									}

									if (gameMode === 1) { // Gepi ellen

										if (COMPUTER) // Keresesi infok (A gep mindig animacioval lep)
										{
											var Score = bestMove.score;

											if (isMate(Score)) {
												$('#game_info').append('<span style="color:darkred"> '+LANGUAGE.mate_in_str+' '+(INFINITE - Math.abs(Score) - 1)+' '+LANGUAGE.mate_in_move+'</span>');
											} else {
												var htmlDepth = bestMove.depth;
												var htmlScore = 0-(Score/100).toFixed(2);
												$('#game_info').append('<span style="color:darkred"> '+LANGUAGE.searched_depth+':'+htmlDepth+' '+LANGUAGE.searched_score+':'+(htmlScore > 0 ? '+' : '')+htmlScore+'</span>');
											}
										}

										if (currentPlayer != yourSide) { // Gepi lepes kovetkezik
											// ertesito update
												SearchStartInfo();
													
											// gepi lepes keresese
												setTimeout(function() { FindMove(0); }, ALPHA_BETA_MAX_IDO < 500 ? 500 : 100);
										}

									} else if (gameMode === 2) { // 2 jatekos jatszik

									}
								
								// Mentes az aktualis allapotrol, kilepes esetere
									window.localStorage.setItem("FEN", START_FEN);
									window.localStorage.setItem("JATEK_MOD", gameMode);
									window.localStorage.setItem("SIDE_KEY_LOW", SideKeyLow);
									window.localStorage.setItem("SIDE_KEY_HIGH", SideKeyHigh);
									window.localStorage.setItem("PIECE_KEYS_LOW", JSON.stringify(PieceKeysLow));
									window.localStorage.setItem("PIECE_KEYS_HIGH", JSON.stringify(PieceKeysHigh));
									window.localStorage.setItem("CASTLE_KEYS_LOW", JSON.stringify(CastleKeysLow));
									window.localStorage.setItem("CASTLE_KEYS_HIGH", JSON.stringify(CastleKeysHigh));
									window.localStorage.setItem("MOVE_HISTORY", JSON.stringify(MOVE_HISTORY));
								} else { // Vege a jateknak toroljuk a mentest
									window.localStorage.removeItem("JATEK_MOD");
									window.localStorage.removeItem("MOVE_HISTORY");
									window.localStorage.removeItem("CASTLE_KEYS_HIGH");
									window.localStorage.removeItem("CASTLE_KEYS_LOW");
									window.localStorage.removeItem("PIECE_KEYS_HIGH");
									window.localStorage.removeItem("PIECE_KEYS_LOW");
									window.localStorage.removeItem("SIDE_KEY_HIGH");
									window.localStorage.removeItem("SIDE_KEY_LOW");
									window.localStorage.removeItem("FEN");
								}

								onMoveLoop = false; // Lepes kesz

							}, 10);
						});
					}, 10);

					return true; // kilepunk
				}
			}
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// FindMove
		function FindMove(USER_HELP) {

			if (JATEK_FOLYAMATBAN === false) { // Jatek vege
				$('#game_info').html(LANGUAGE.game_over);
				return false;
			} else if (maxSearchTime !== 0) { // Nem indithat dupla keresest a user
				return false;
			} else if (gameMode !== 1) { // 2 jatekos jatszik egymas ellen
				return false;
			}

			if (USER_HELP) { // BUGFIX: uj jatek vizsgalat utan a gepi idovel keresett volna a gep
				if (currentPlayer !== yourSide && gameMode === 1) { // Gepi lepes kozben nem segitunk
					return false;
				}
				helpLoop = true;
			} else {
				helpLoop = false;
			}

			maxSearchTime = ALPHA_BETA_MAX_IDO; // beallitott ido ezred masodpercben

			var gameLine = printGameLine(); // Lepesvonal betoltes
			bestMove = BookMove(gameLine); // Nyitasok Konyvbol

			if (bestMove) { // Ha volt a konyvben egyezo sor

				var book_move = bestMove.split('-');

				$('#game_info').html(USER_HELP ? LANGUAGE.help_from_book : LANGUAGE.move_from_book);

				setTimeout(function() {
					onMove(parseInt(book_move[0]), parseInt(book_move[1]), false, false, false); // maga a lepes
				}, (USER_HELP ? 0 : 500));

				return false;
			}

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			if (USER_HELP) { // Segitseg maximum 2 masodpercig
				maxSearchTime = maxSearchTime > 2000 ? 2000 : maxSearchTime;
			}

			var maxSearchDepth = 64; // Max keresesi melyseg

			if (maxSearchTime < 1000) { // 1 masodperc alatti szint
				maxSearchDepth = maxSearchTime / 100;
				maxSearchTime = 1000;
			}

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Hatterben kereses Worker-el
			if (InitBackgroundEngine())
			{
				maxSearchDepth = maxSearchDepth < 64 ? maxSearchDepth : 0; // Hack
				backgroundEngine.postMessage('position startpos moves '+gameLine);
				backgroundEngine.postMessage('go movetime '+maxSearchTime+' depth '+maxSearchDepth);
			}
		// Kereses Worker nelkul
			else
			{
				SearchPosition(maxSearchDepth); // Kereses inditas

				MOVE_HISTORY.splice(moveCount); // Elozmeny torlese a jatekmenteshez

				onMove(FROMSQ(bestMove.move), TOSQ(bestMove.move), PROMOTED(bestMove.move), true, false);
			}
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// Opben BOOK >> GEP ELLENI NYITASOK
		function printGameLine() {
			var gameLine = '';
			for (var moveNum = 0; moveNum < moveCount; ++moveNum) {
				gameLine += FormatMove(MOVE_HISTORY[moveNum].move)+' ';
			}
			return $.trim(gameLine);
		}


		function LineMatch(BookLine, gameLine) {
			for (var len = 0; len < gameLine.length; ++len) {
				if (len >= BookLine.length) { return false;	}	
				if (gameLine[len] != BookLine[len]) { return false;	}	
			}
			return true;
		}


		function BookMove(gameLine) {
			var bookMoves = [];
			var lengthOfLineHack = gameLine.length;
			
			if (gameLine.length == 0) lengthOfLineHack--;
			
			for (var bookLineNum = 0; bookLineNum < brd_bookLines.length; ++bookLineNum) {
				if (LineMatch(brd_bookLines[bookLineNum], gameLine) === true) {
					var move = brd_bookLines[bookLineNum].substr(lengthOfLineHack + 1, 4);
					if (move.length == 4) {
						var from = $('div[alt="'+move.substr(0,2)+'"]').attr('data-square');
						var to = $('div[alt="'+move.substr(2,2)+'"]').attr('data-square');
						bookMoves.push(from+'-'+to);
					} 
				}
			}
				
			if (bookMoves.length == 0) return false;
			
			var num = Math.floor(Math.random()*bookMoves.length);
			
			return bookMoves[num];
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// Gep_Erosseg Allitasa
		function Gep_Erosseg(id) {

			if (moveCount < 2 || JATEK_FOLYAMATBAN === false)
			{
				var maxIdo = parseInt(id);

				if (maxIdo > 0 && maxIdo < 30001)
				{
					ALPHA_BETA_MAX_IDO = maxIdo;

					window.localStorage.setItem("GEP_EROSSEG", ALPHA_BETA_MAX_IDO); // Erosseg mentese
				}
			}
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// Back_Step
		function Back_Step() {

			if (onMoveLoop === false && helpLoop === false && moveCount > 1 && JATEK_FOLYAMATBAN === true)
			{
				if (maxSearchTime !== 0) { // ha epp keres a gep
					if (InitBackgroundEngine()) { // Worker leallitasa
						WorkerStop();
						maxSearchTime = 0;
						ChessEngineRestart(); // Sakk motor ujrainditas
					} else { // Worker nelkul meg kell varnunk a kereses veget
						return false;
					}
					unMakeMove(); // jatekos lepes visszavonasa
				} else {
					unMakeMove(); // gepi lepes visszavonasa
					unMakeMove(); // jatekos lepes visszavonasa
				}

				START_FEN = boardToFEN(); // FEN letrehozasa
				MOVE_HISTORY.splice(moveCount); // elozmeny torlese

				if (MOVE_HISTORY.length != 0) { // ha van meg elozmeny

					var LAST_MOVE = MOVE_HISTORY[moveCount-1]; // legutolso lepes

					window.localStorage.setItem("FEN", START_FEN); // Fen mentes frissitese
					window.localStorage.setItem("MOVE_HISTORY", JSON.stringify(MOVE_HISTORY)); // Elozmeny frissitese

					drawBoard(CHESS_BOARD, LAST_MOVE.move); // Tabla rajzolasa

				} else { // Ha nincs tobb elozmeny akkor toroljuk a mentest

					window.localStorage.removeItem("JATEK_MOD");
					window.localStorage.removeItem("MOVE_HISTORY");
					window.localStorage.removeItem("CASTLE_KEYS_HIGH");
					window.localStorage.removeItem("CASTLE_KEYS_LOW");
					window.localStorage.removeItem("PIECE_KEYS_HIGH");
					window.localStorage.removeItem("PIECE_KEYS_LOW");
					window.localStorage.removeItem("SIDE_KEY_HIGH");
					window.localStorage.removeItem("SIDE_KEY_LOW");
					window.localStorage.removeItem("FEN");

					drawBoard(CHESS_BOARD, NOMOVE); // Tabla rajzolasa

				}
			}
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// 3 lepesismetleses dontetlen
		function ThreeFoldRep() {
			var r = 0;
			for (var index = 0; index < moveCount; index++)	{
				if (MOVE_HISTORY[index].hashKeyLow == brd_hashKeyLow 
				&& MOVE_HISTORY[index].hashKeyHigh == brd_hashKeyHigh) {
					r++;
				}
			}
			return r;
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// Jatek vegenek ellenorzese
		function GameOver() {
			for (var from_index = 0; from_index < 120; from_index++)
			{
				if (CHESS_BOARD[from_index] && (CHESS_BOARD[from_index] & 0x8) === currentPlayer) // AKI EPP LEPHET
				{
					for (var next_index = 0; next_index < 120; next_index++)
					{
						if (validateMove(from_index, next_index, currentPlayer))
						{
							return false; // nincs vege
						}
					}
				}
			}
			return true;
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// Worker Kereses Informacio
		function WorkerSearchInfo(startTime) {
			var max = ALPHA_BETA_MAX_IDO / 1000;
			MoveTime = (Date.now() - startTime);
			if (helpLoop && max > 2) max = 2;

			$('#game_info').html(LANGUAGE.search_msg_1+' ('+max+'/'+Math.round(MoveTime/1000)+' '+LANGUAGE.search_msg_2+' '+(bestMove ? bestMove.depth : 0)+')');
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// Kereses inditas elotti info
		function SearchStartInfo() {
			var max = ALPHA_BETA_MAX_IDO / 1000;

			if (InitBackgroundEngine())
			$('#game_info').html(LANGUAGE.search_msg_1+' ('+max+'/0 '+LANGUAGE.search_msg_2+' 0)');
			else
			$('#game_info').html(LANGUAGE.search_msg_1+' ('+max+' sec)');
		}



// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// Worker (.js hatter futtatas) leallitasa
		function WorkerStop() {
			clearInterval(WorkerSearch);
			backgroundEngine.terminate();
			backgroundEngine = null;
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// Sakk motor ujrainditas
		function ChessEngineRestart() {
			if (InitBackgroundEngine()) { // Worker-el
				backgroundEngine.postMessage('ucinewgame tanky');
				backgroundEngine.postMessage(['HashKeys', SideKeyLow, SideKeyHigh, PieceKeysLow, PieceKeysHigh, CastleKeysLow, CastleKeysHigh]);
			}
			InitEnginSearch(); // UI szamara mindig lefut!
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// Worker (.js hatterbe futas)
		function InitBackgroundEngine() {

			if (!backgroundEngineValid) {
				return false;
			}

			if (backgroundEngine == null)
			{
				backgroundEngineValid = true;
				try 
				{
					backgroundEngine = new Worker("js/tomitankChess.js");

					backgroundEngine.onmessage = function (e) {
						if (e.data[0] == "bestMove")
						{
							clearInterval(WorkerSearch); // Szamlalas leallitasa

							bestMove = e.data[1]; // Legjobb lepes

							onMove(FROMSQ(bestMove.move), TOSQ(bestMove.move), PROMOTED(bestMove.move), true, false);
						}
						else if (e.data[0] == "SearchInfo")
						{
							bestMove = e.data[1]; // Keresesi Info
						}
						else if (e.data[0] == "StartedTime")
						{
							WorkerSearch = setInterval(function() { // Keresesi Info 0.2s
								WorkerSearchInfo(e.data[1]);
							}, 200);
						}
						else if (e.data[0] == "Redraw")
						{
							drawBoard(e.data[1], NOMOVE); // Tabla rajzolasa
						}
						else if (e.data[0] == "debug")
						{
							global_info('Debugger üzenet:<br>'+e.data[1]+ // Debug!
							'<a class="ok_gomb" href="javascript:void(0)" alt="global_info_close">RENDBEN</a>');
						}
					}

					backgroundEngine.error = function (e)
					{
						alert("Hiba a Worker Feldolgozasaban:" + e.message);
					}
				} 
				catch (error)
				{
					backgroundEngineValid = false;
				}
			}

			return backgroundEngineValid;
		}

