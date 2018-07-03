// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
// Texel Tuning Method by tomitank
// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	var K         = 0;
	var numFens   = 0;
	var results   = new Array();
	var tuneEvals = new Array();
	var positions = new Array();

	var params = [
	//	{ name : 'pawn',   value :   80 },
		{ name : 'knight', value :  325 },
		{ name : 'bishop', value :  325 },
		{ name : 'rook',   value :  500 },
		{ name : 'queen',  value : 1000 }
	];

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	$(document).ready(function() {

		$.ajax({
			cache : false,
			mimeType: "text/plain",
			url : "js/tuning_fen.txt",
			success: function (txt) {

				positions = txt.split('\n');

			}, complete: function() {

				InitHashKeys();
				InitEnginSearch();

				numFens = positions.length;

				console.log(numFens+' FENs loaded..please wait..');

				for (var i = 0; i < numFens; i++) { // inicializalas

					var trimed = $.trim(positions[i]);
					var result = trimed.substr(-5, 3);
					results[i] = result == '1-0' ? 1 : result == '0-1' ? 0 : 0.5;

					tuneEvals[i] = tuning_evaluation(positions[i]); // ertekeles
				}

				K = compute_optimal_k();

				console.log('Optimal K: '+K);

				run_texel_tuning(); // hangolas..

				console.log('Tuning finished!');

				for (var i = 0; i < params.length; i++) // eredemenyek kiirasa
				{
					console.log('Final '+params[i].name+' value: '+params[i].value);
				}
			}
		});

	});

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function run_texel_tuning() {

		var best_error = total_eval_error(K); // alap hiba

		var improved = true;
		var iteration = 1;

		while (improved) {

			improved = false;

			console.log('tuning iteration: '+iteration++);

			for (var i = 0; i < params.length; i++) {

				params[i].value++;

				var this_error = tune_error(i); // vizsgalat..
				if (this_error < best_error) { // kisebb hiba
					best_error = this_error;
					improved = true;

				} else { // nagyobb hiba...masik irany

					params[i].value -= 2;

					var this_error = tune_error(i); // vizsgalat..
					if (this_error < best_error) { // kisebb hiba
						best_error = this_error;
						improved = true;
					}
				}

				console.log(params[i].name+': '+params[i].value);
			}
		}
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function parameter_update(idx) {

		if (idx <= -1) return;

		var name  = params[idx].name;
		var value = params[idx].value;

		if (name == 'pawn') {

			PieceValue[WHITE_PAWN] = value;
			PieceValue[BLACK_PAWN] = value;

		} else if (name == 'knight') {

			PieceValue[WHITE_KNIGHT] = value;
			PieceValue[BLACK_KNIGHT] = value;

		} else if (name == 'bishop') {

			PieceValue[WHITE_BISHOP] = value;
			PieceValue[BLACK_BISHOP] = value;

		} else if (name == 'rook') {

			PieceValue[WHITE_ROOK] = value;
			PieceValue[BLACK_ROOK] = value;

		} else if (name == 'queen') {

			PieceValue[WHITE_QUEEN] = value;
			PieceValue[BLACK_QUEEN] = value;

		}
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function compute_optimal_k() { // by Andrew Grant

		var start = -10.0, end = 10.0, delta = 1.0;
		var curr = start, this_error = 0;
		var best_error = total_eval_error(start);

		for (var i = 0; i < 10; i++) {
			curr = start - delta;
			while (curr < end) {
				curr = curr + delta;
				this_error = total_eval_error(curr);
				if (this_error <= best_error) {
					best_error = this_error;
					start = curr;
				}
			}

			end = start + delta;
			start = start - delta;
			delta = delta / 10.0;
		}

		return start;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function tuning_evaluation(pos) {

		START_FEN = pos;

		ClearForSearch();

		moveCount = 0;
		brd_fiftyMove = 0;
		MOVE_HISTORY = new Array();

		CHESS_BOARD = FENToBoard();

		var inCheck = isCheck(currentPlayer);

		var value = Quiescence(-INFINITE, INFINITE, DEPTH_ZERO, inCheck);

		return currentPlayer === WHITE ? value : -value;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function tune_error(param) {

		parameter_update(param);

		var used = 0;
		var total = 0.0;

		for (var i = 0; i < numFens; i++) {

			var eval = tuning_evaluation(positions[i]);

			if (good_tunning_value(eval) === true)  {
				used++;
				total += Math.pow(results[i] - Sigmoid(K, eval), 2);
			}
		}

		return total / used;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function total_eval_error(K) {

		var used = 0;
		var total = 0.0;

		for (var i = 0; i < numFens; i++) {

			var eval = tuneEvals[i];

			if (good_tunning_value(eval) === true)  {
				used++;
				total += Math.pow(results[i] - Sigmoid(K, eval), 2);
			}
		}

		return total / used;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function Sigmoid(K, S) {
		return 1.0 / (1.0 + Math.pow((-K * S / 400), 10));
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function good_tunning_value(value) {
		return value >= -600 && value <= 600;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
