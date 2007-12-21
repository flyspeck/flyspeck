<?php
/* rewrites page titles that are not permitted by MediaWiki */
function rewriteToLegalTitle($title) {
	/* modeled to match $wgLegalTitle */
	return str_replace(array('_', '[', ']', '{', '}', '|', '#', '<', '>', '%', '+', '?', '~'),
			   array('_usc', '_sbo', '_sbc', '_cbo', '_cbc', '_bar', '_hash', '_lt', '_gt', '_pct', '_plus', '_q', '_til'), $title);
}

/* transforms any non-Twelf symbol into a link to the respective symbol page*/
function linkSymbol($symbol) {
	$escapedSymbol = wfEscapeWikiText($symbol);

	$symbolPage = Title::newFromText(TWELF_PROJECT . '/' . rewriteToLegalTitle($symbol));
	if ($symbolPage->exists()) {
		/* find out whether this page is an instance of the category Symbol */
		$dbr = wfGetDB( DB_SLAVE );
		$categorylinks = $dbr->tableName( 'categorylinks' );
		$id = $symbolPage->getArticleId();
		if ($dbr->query("SELECT COUNT(*) FROM page, $categorylinks WHERE page_id=$id AND cl_to='Symbol' AND page_id=cl_from") == 1) {
			$target = TWELF_PROJECT . '/' . rewriteToLegalTitle($symbol);
			return "[[uses symbol::$target|$escapedSymbol]]";
		}
	}
	return $escapedSymbol;
}

/* rewrites all tokens in a Twelf source code line to links */
function processTwelfLine($line) {
	// TODO this regular expression needs improvement
	return ' ' . preg_replace_callback('/[^ \n\t.()0-9][^ \n\t.()]*/', create_function('$matches', 'return linkSymbol($matches[0]);'), $line);
}

class TwelfUpload extends SpecialPage
{
        function TwelfUpload() {
                SpecialPage::SpecialPage("TwelfUpload", "import");
                self::loadMessages();
        }

	function createWikiPage($title, $comment, $wikiText) {
		global $wgUser;

		$revision = new WikiRevision;
		$revision->setUsername($wgUser->getName());
		$revision->setTitle($title);
		$revision->setTimestamp(wfTimestampNow());
		$revision->setComment($comment);
		$revision->setMinor(false);
		$revision->setText($wikiText);

		$dbw = wfGetDB(DB_MASTER);
		$result = $dbw->deadlockLoop(array(&$revision, 'importOldRevision'));
		if ($result) {
			$nullRevision = Revision::newNullRevision($dbw, $title->getArticleId(), $comment, false);
			$nullRevision->insertOn($dbw);
			$article = new Article($title);
			$article->updateRevisionOn($dbw, $nullRevision);
		}
		return $result;
	}

	function createMathPage($title, $type, $comment, $wikiText) {
		global $wgOut;

		$pageTitle = $title;

		/* Adjust the title and content of the page to be created */
		if ($type == 'Category') {
			$wikiTitle = Title::newFromText('Category:' . TWELF_PROJECT . "/$title");
		}
		else {
			if ($type == 'Definition') {
				$pageTitle = "$title-def";
				$wikiText .= "\n[[defines::" . TWELF_PROJECT . "/$title| ]]";
			}
			$wikiTitle = Title::newFromText(TWELF_PROJECT . "/$pageTitle.elf");
			$wikiText .= "\n[[Category:$type]]";
		}

		// $wgOut->addHTML("<li><pre>Adding page $pageTitle with text $wikiText</pre></li>");
		if (self::createWikiPage($wikiTitle, $comment, $wikiText)) {
			$log = new LogPage('twelfupload');
			// TODO use different message if category is created
			$log->addEntry('upload-twelf', $wikiTitle, "");

			/* For a definition, also recursively create the symbol that is defined */
			if ($type == 'Definition') {
				$definitionPage = TWELF_PROJECT . "/$title-def";
				$wikiText = <<<EOT
 [[has definition::$definitionPage|$title]]
EOT;

				// TODO maybe we need a different comment here
				self::createMathPage($title, 'Symbol', $comment, $wikiText);
			}

			if ($type != 'Category') {
				/* fake reference to a TeX page */
				$texTitle = Title::newFromText(TWELF_PROJECT . "/$pageTitle.tex");

				/* add the container page for annotations, if it does not yet exist */
				$containerTitle = Title::newFromText(TWELF_PROJECT . "/$pageTitle");
				if (!$containerTitle->exists()) {
					$comment = wfMsgForContent('twelfupload-create-container-comment', $filename);
					$wikiText = <<<EOT
== [[written in::Twelf]] ==
{{:$wikiTitle}}

== [[written in::LaTeX]] ==
{{:$texTitle}}

== Annotations ==

EOT;

					if (self::createWikiPage($containerTitle, $comment, $wikiText)) {
						$log->addEntry('create-container', $containerTitle, "");
					}
				}

				$wgOut->addHTML('<li>page <a href="' . $containerTitle->getLocalUrl() . '">' . $pageTitle . '</a></li>');
			}
			else {
				$wgOut->addHTML('<li>category <a href="' . $wikiTitle->getLocalUrl() . '">' . $title . '</a></li>');
			}
		}
	}

 	function importPage($page, $filename, $wikiText = '') {
		global $wgUser, $wgOut;

		global $wgShowExceptionDetails;
		$wgShowExceptionDetails = true;

		/* get the metadata */
		switch ($page->tagName) {
			case 'section':
				/* handle type declarations as well as definitions */
				if (preg_match('/^([^=: ]+) ?([:=])/', $wikiText, $matches)) {
					$title = rewriteToLegalTitle($matches[1]);
					/* pad the actual Twelf listing with spaces for listing formatting and escape other wiki formatting */
					$wikiText = preg_replace_callback('/^([^%]*)((?:%.*)?)$/m', create_function('$replace_matches', 'return " " . processTwelfLine($replace_matches[1]) . $replace_matches[2];'), $wikiText);
					// TODO tokenize the text, replacing symbols by links to their respective pages. Note that then only the text _between_ these tokens has to be escaped!
					/* prepend the actual title, if the title was rewritten */
					if ($title != $matches[1]) {
						$wikiText = "'''''Actual title of this page: " . wfEscapeWikiText($matches[1]) . "'''''\n----\n" . $wikiText;
					}
					// TODO For now, we only have symbol definitions. Later, we may have lemma definitions, i.e. proofs.
					$type = $matches[2] == '=' ? 'Definition' : 'Symbol';
				}
				else {
					return false;
					// FIXME throw some exception
				}
				$topic = $page->getAttribute('topic');
				$wikiText .= "\n[[Category:" . TWELF_PROJECT . "/$topic]]";
				/* we distinguish lemmas from things that are "just" symbols */
				if ($type == 'Symbol' && preg_match('/^lemma-/', $title)) {
					$type = 'Lemma';
				}
				break;
			case 'topic':
				$title = $page->getAttribute('name');
				$type = 'Category';
				$wikiText = '[[Category:' . TWELF_PROJECT . '/' . $page->getAttribute('parent') . ']]';
				break;
			default:
				// does not occur with the current implementation of execute
		}

		/* add/overwrite the math/Twelf page itself */
		$comment = wfMsgForContent('twelfupload-upload-twelf-comment', $filename);
		self::createMathPage($title, $type, $comment, $wikiText);
	}
 
        function execute( $par ) {
                global $wgRequest, $wgOut;
 
                $this->setHeaders();
 
		if ($wgRequest->wasPosted() && $wgRequest->getVal('action') == 'submit') {
			$source = ImportStreamSource::newFromUpload("twelffile");
			$filename = $_FILES['twelffile']['name'];
			
			if (WikiError::isError($source)) {
				$wgOut->addWikiText(wfEscapeWikiText($source->getMessage()));
			}
			else {
				/* Accessing mHandle is dirty, but allows us to
				 * reuse ImportStreamSource */
				$handle = $source->mHandle;
				$wgOut->addHTML("<p>Imported:</p><ul>");
				while (!feof($handle)) {
					// We assume that the lines of the file are quite short
					$buffer = fgets($handle);
					if (preg_match('/^%% ((?:section|topic).*)$/', $buffer, $matches)) {
						if ($page) {
							self::importPage($page, $filename, $wikiBuffer);
						}
						/* treat the section separator as an XML element to accommodate parsing */
						$dom = new DOMDocument();
						$dom->loadXML("<$matches[1]/>");
						$page = $dom->documentElement;
						$wikiBuffer = "";
					}
					else {
						$wikiBuffer .= $buffer;
					}
			    	}
				if ($page) {
					self::importPage($page, $filename, $wikiBuffer);
				}
			        fclose($handle);
				$wgOut->addHTML("</ul>");
			}
		}
		else {
			$action = $this->getTitle()->getLocalUrl('action=submit');
			$wgOut->addHTML(<<<EOH
<form action="{$action}" method="post" enctype="multipart/form-data">
<input type="hidden" name="MAX_FILE_SIZE" value="1048576" />
<label for="#twelffile">Twelf file:</label>
<input type="file" name="twelffile" id="twelffile"/><br/>
<input type="submit"/>
</form>
EOH
			);
		}
        }
 
        function loadMessages() {
                static $messagesLoaded = false;
                global $wgMessageCache;
                if ( !$messagesLoaded ) {
                        $messagesLoaded = true;
 
                        require( dirname( __FILE__ ) . '/TwelfUpload.i18n.php' );
                        foreach ( $allMessages as $lang => $langMessages ) {
                                $wgMessageCache->addMessages( $langMessages, $lang );
                        }
                }
                return true;
        }
}
