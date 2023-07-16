Rules for branches
==================

  * Use a branch name of the form `⟨type⟩/⟨topic⟩`. Here, `⟨type⟩`
    refers to the type of contribution as given by the label of the form
    `type: ⟨type⟩` of the pull request associated with the branch.

  * For the `⟨topic⟩` part of the branch name, use only lowercase Latin
    letters, Arabic numerals, and ASCII dashes, with the latter also
    serving as separators of words.


Rules for commits[^original-commit-rules]
=========================================

  * Put only related changes into a single commit.

  * Use correct spelling for the author name (for example, include all
    diacritics).

  * Use Markdown for the entire commit message (subject line and body).

  * Separate the subject line from the body with a blank line.

  * Limit the subject line to 58 characters.

  * Start the subject line with a capital letter.

  * Do not end the subject line with a period.

  * Use the imperative mood in the subject line.

  * Wrap the body at 72 characters.

  * Use the body to explain the *what* and *why*, not the *how*.

  * When merging another branch into your branch, use a subject line of
    the following form:

        Merge `⟨other-branch⟩` into `⟨your-branch⟩`

  * When merging the branch of a pull request into the `master` branch,
    put the title of the pull request into the body of the commit
    message and use a subject line of the following form:

        Merge `⟨branch⟩` of pull request #⟨pull-request-number⟩ into `master`

    Here, `⟨branch⟩` refers to the name of the branch without the GitHub
    account name component.

[^original-commit-rules]:
    Several of these rules have been taken from
    https://chris.beams.io/posts/git-commit/#seven-rules.
